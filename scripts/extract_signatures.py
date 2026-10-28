#!/usr/bin/env python3
"""Extract declaration signatures from the MathEconLib docgen SQLite database.

The default mode writes one Markdown file per top-level MathEconLib module
into the `--output` directory, plus an index at `README.md`. Use
`--single MODULE` to extract a single dotted module prefix into one flat
`--output` file instead.

For structures, the header, parent types, and direct fields are shown.
"""

from __future__ import annotations

import argparse
import json
import re
from contextlib import closing
import shutil
import sqlite3
import subprocess
import sys
import tempfile
from pathlib import Path

from build_docs import build_docs, open_readonly

REPO_ROOT = Path(__file__).resolve().parent.parent
REQUIRED_COLUMNS = {
    "modules": {"name"},
    "name_info": {"module_name", "position", "kind", "name", "type", "sorried", "render"},
    "declaration_markdown_docstrings": {"module_name", "position", "text"},
    "declaration_args": {"module_name", "position", "sequence", "binder"},
    "structures": {"module_name", "position"},
    "structure_parents": {"module_name", "position", "sequence", "type"},
    "structure_fields": {"module_name", "position", "sequence", "proj_name", "type", "is_direct"},
    "structure_field_args": {"module_name", "position", "field_sequence", "arg_sequence", "binder"},
    "definition_equations": {"module_name", "position", "sequence", "code"},
}


# ---------------------------------------------------------------------------
# Binary blob decoder for RenderedCode (TaggedText RenderedCode.Tag)
#
# Serialized via leansqlite's ToBinary instances.  Format:
#   Nat          = LEB128 (high‐bit continuation)
#   String       = Nat(utf8_byte_len) ++ raw_bytes
#   Array α      = Nat(size) ++ elements
#   Name         = 0 (anonymous) | 1 + Name + String (str) | 2 + Name + Nat (num)
#   Tag          = 0 keyword | 1 string | 2 const(Name) | 3 sort(none)
#                  | 4 sort(Type) | 5 sort(Prop) | 6 sort(Sort) | 7 otherExpr
#   TaggedText   = 0 + String (text) | 1 + Tag + TaggedText (tag) | 2 + Array(TaggedText) (append)
# ---------------------------------------------------------------------------


class _BlobReader:
    __slots__ = ("data", "pos")

    def __init__(self, data: bytes):
        self.data = data
        self.pos = 0

    def byte(self) -> int:
        b = self.data[self.pos]
        self.pos += 1
        return b

    def nat(self) -> int:
        result = 0
        shift = 0
        while True:
            b = self.byte()
            if b >= 128:
                result |= (b & 0x7F) << shift
            else:
                result |= b << shift
                break
            shift += 7
        return result

    def string(self) -> str:
        n = self.nat()
        if self.pos + n > len(self.data):
            raise ValueError("truncated string")
        s = self.data[self.pos : self.pos + n].decode("utf-8")
        self.pos += n
        return s

    # -- Name --
    def name(self) -> str:
        tag = self.byte()
        if tag == 0:  # anonymous
            return ""
        elif tag == 1:  # str
            parent = self.name()
            component = self.string()
            return f"{parent}.{component}" if parent else component
        elif tag == 2:  # num
            parent = self.name()
            n = self.nat()
            return f"{parent}.{n}" if parent else str(n)
        else:
            raise ValueError(f"Name: unexpected tag {tag}")

    # -- RenderedCode.Tag (skip, we only want text) --
    def skip_tag(self) -> None:
        tag = self.byte()
        if tag == 2:  # const — has a Name payload
            self.name()
        elif tag not in (0, 1, 3, 4, 5, 6, 7):
            raise ValueError(f"RenderedCode.Tag: unexpected tag {tag}")
        # 0,1,3,4,5,6,7 are nullary after the byte

    # -- TaggedText → plain text --
    def tagged_text(self) -> str:
        tag = self.byte()
        if tag == 0:  # text
            return self.string()
        elif tag == 1:  # tag
            self.skip_tag()
            return self.tagged_text()
        elif tag == 2:  # append
            n = self.nat()
            return "".join(self.tagged_text() for _ in range(n))
        else:
            raise ValueError(f"TaggedText: unexpected tag {tag}")


def decode_rendered_code(data: bytes) -> str:
    """Decode a RenderedCode blob to plain text."""
    try:
        reader = _BlobReader(data)
        result = reader.tagged_text()
        if reader.pos != len(data):
            raise ValueError("trailing bytes")
        return result
    except (IndexError, ValueError, RecursionError) as error:
        raise ValueError(f"Malformed RenderedCode blob: {error}") from error


# ---------------------------------------------------------------------------
# Signature emission
# ---------------------------------------------------------------------------


def render_module_signatures(
    conn: sqlite3.Connection, mod: str, show_docs: bool
) -> tuple[list[str], int]:
    """Render the signatures for a single module. Returns (lines, decl_count)."""
    decls = conn.execute(
        """SELECT n.position, n.kind, n.name, n.type, n.sorried,
                  d.text
           FROM name_info n
           LEFT JOIN declaration_markdown_docstrings d
             ON d.module_name = n.module_name AND d.position = n.position
           WHERE n.module_name = ? AND n.render = 1
           ORDER BY n.position""",
        (mod,),
    ).fetchall()

    if not decls:
        return [], 0

    lines: list[str] = [f"## {mod}", ""]
    count = 0
    for pos, kind, name, type_blob, sorried, docstring in decls:
        type_str = decode_rendered_code(type_blob) if type_blob else ""
        sorry_mark = " [sorry]" if sorried else ""

        arg_rows = conn.execute(
            """SELECT binder FROM declaration_args
               WHERE module_name = ? AND position = ?
               ORDER BY sequence""",
            (mod, pos),
        ).fetchall()
        binders = " ".join(decode_rendered_code(b) for (b,) in arg_rows if b)
        head = f"{kind} {name}"
        if binders:
            head = f"{head} {binders}"
        is_struct = conn.execute(
            "SELECT 1 FROM structures WHERE module_name = ? AND position = ?",
            (mod, pos),
        ).fetchone()

        if is_struct:
            parents = conn.execute(
                """SELECT type FROM structure_parents
                   WHERE module_name = ? AND position = ?
                   ORDER BY sequence""",
                (mod, pos),
            ).fetchall()
            if parents:
                head += " extends " + ", ".join(decode_rendered_code(p) for (p,) in parents)
        sig = f"{head} : {type_str}{sorry_mark}" if type_str else f"{head}{sorry_mark}"

        if is_struct:
            fields = conn.execute(
                """SELECT sf.proj_name, sf.type, sf.sequence
                   FROM structure_fields sf
                   WHERE sf.module_name = ? AND sf.position = ? AND sf.is_direct = 1
                   ORDER BY sf.sequence""",
                (mod, pos),
            ).fetchall()

            lines.append("```")
            lines.append(sig)
            if fields:
                lines.append("  where")
                for fname, ftype_blob, field_sequence in fields:
                    ftype = decode_rendered_code(ftype_blob) if ftype_blob else "?"
                    field_args = conn.execute(
                        """SELECT binder FROM structure_field_args
                           WHERE module_name = ? AND position = ? AND field_sequence = ?
                           ORDER BY arg_sequence""",
                        (mod, pos, field_sequence),
                    ).fetchall()
                    binders = " ".join(decode_rendered_code(b) for (b,) in field_args if b)
                    field_head = f"{fname} {binders}" if binders else fname
                    lines.append(f"    {field_head} : {ftype}")
            lines.append("```")
        else:
            eqs = conn.execute(
                """SELECT code FROM definition_equations
                   WHERE module_name = ? AND position = ?
                   ORDER BY sequence""",
                (mod, pos),
            ).fetchall()
            eq_texts: list[str] = []
            for (eq_blob,) in eqs:
                if eq_blob:
                    eq_texts.append(decode_rendered_code(eq_blob))

            lines.append(f"- `{sig}`")
            for eq in eq_texts:
                lines.append(f"  - `{eq}`")

        if show_docs and docstring:
            lines.append(f"  > {docstring.strip()}")
        count += 1
    lines.append("")
    return lines, count


def list_modules(conn: sqlite3.Connection, prefix: str) -> list[str]:
    return [
        row[0]
        for row in conn.execute(
            "SELECT name FROM modules WHERE name = ? OR (name >= ? AND name < ?) ORDER BY name",
            (prefix, prefix + ".", prefix + "/"),
        )
    ]


def render_subtree(
    conn: sqlite3.Connection, root: str, show_docs: bool
) -> tuple[list[str], int, int]:
    """Render all modules at or under `root` as a flat list of markdown lines.
    Returns (lines, total_decls, n_modules)."""
    modules = list_modules(conn, root)
    body: list[str] = [
        f"# {root} — Declaration Signatures",
        "",
        "Auto-extracted from `api-docs.db` by `scripts/extract_signatures.py`.",
        "",
    ]
    total = 0
    for mod in modules:
        mod_lines, count = render_module_signatures(conn, mod, show_docs)
        if mod_lines:
            body.extend(mod_lines)
            total += count
    body.append(f"---\n*{total} declarations across {len(modules)} modules.*\n")
    return body, total, len(modules)


def line_count(body: list[str]) -> int:
    """Effective number of lines once the body is joined."""
    return sum(s.count("\n") for s in body) + len(body)


def immediate_children(conn: sqlite3.Connection, root: str) -> list[str]:
    """Distinct module names obtained by appending one segment to `root`."""
    seen: set[str] = set()
    for name in list_modules(conn, root):
        if name == root:
            continue
        rest = name[len(root) + 1 :]
        head = rest.split(".", 1)[0]
        seen.add(f"{root}.{head}")
    return sorted(seen)


def write_single(
    conn: sqlite3.Connection, prefix: str, output: Path, show_docs: bool
) -> None:
    body, total, n_mods = render_subtree(conn, prefix, show_docs)
    print(f"Found {n_mods} modules for {prefix}")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text("\n".join(body), encoding="utf-8")
    print(f"Wrote {total} signatures to {output}")


def write_node(
    conn: sqlite3.Connection,
    root: str,
    out_dir: Path,
    max_lines: int,
    show_docs: bool,
    depth: int,
) -> dict:
    """Write `root` (and all submodules) into `out_dir`, either as a flat
    <short>.md file or as a recursive <short>/ subdirectory if the flat
    rendering would exceed `max_lines` and `root` has multiple subgroups.
    Returns a dict describing the result for index assembly."""
    short = root.rsplit(".", 1)[-1]
    body, total, n_mods = render_subtree(conn, root, show_docs)
    lines = line_count(body)

    children = immediate_children(conn, root)
    splittable = len(children) > 1 and any(c != root for c in children)
    indent = "  " * depth

    if max_lines and lines > max_lines and splittable:
        subdir = out_dir / short
        subdir.mkdir(parents=True, exist_ok=True)
        print(f"{indent}{short}/  ({lines} lines, splitting into {len(children)} subgroups)")
        rows = write_split(conn, root, subdir, max_lines, show_docs, depth + 1)
        return {
            "kind": "dir",
            "short": short,
            "link": f"{short}/README.md",
            "modules": n_mods,
            "decls": total,
            "lines": lines,
            "child_rows": rows,
        }
    else:
        filename = f"{short}.md"
        (out_dir / filename).write_text("\n".join(body), encoding="utf-8")
        print(f"{indent}{filename}  ({total} decls, {n_mods} modules, {lines} lines)")
        return {
            "kind": "file",
            "short": short,
            "link": filename,
            "modules": n_mods,
            "decls": total,
            "lines": lines,
        }


def write_split(
    conn: sqlite3.Connection,
    root: str,
    out_dir: Path,
    max_lines: int,
    show_docs: bool,
    depth: int = 0,
    revision: str | None = None,
) -> list[dict]:
    """Split `root` into per-immediate-child files (recursively if needed).
    Writes README.md as the index. Returns the list of result rows."""
    out_dir.mkdir(parents=True, exist_ok=True)
    children = immediate_children(conn, root)
    if depth == 0:
        print(f"Splitting {root} into {len(children)} children at {out_dir}")

    rows: list[dict] = []
    for child in children:
        rows.append(write_node(conn, child, out_dir, max_lines, show_docs, depth))

    own_lines, own_count = render_module_signatures(conn, root, show_docs)
    own_module = conn.execute("SELECT 1 FROM modules WHERE name = ?", (root,)).fetchone()
    grand_modules = sum(r["modules"] for r in rows) + int(own_module is not None)
    grand_decls = sum(r["decls"] for r in rows) + own_count
    index: list[str] = [
        f"# {root} — Signature Index",
        "",
        "Per-module declaration signatures, auto-extracted from `api-docs.db`.",
    ]
    if depth == 0:
        index.append(
            "Regenerate via `python3 scripts/extract_signatures.py` "
            "(default mode splits into this directory)."
        )
    if depth == 0 and revision is not None:
        index += ["", f"Source revision: `{revision}`"]
    index += [
        "",
        f"**Totals: {grand_decls} declarations across {grand_modules} modules.**",
        "",
        "| Module | Entry | Modules | Declarations | Lines |",
        "|---|---|---:|---:|---:|",
    ]
    for r in rows:
        index.append(
            f"| `{root}.{r['short']}` | [{r['link']}]({r['link']}) "
            f"| {r['modules']} | {r['decls']} | {r['lines']} |"
        )
    index.append("")
    # A split parent can define declarations as well as import children.
    # Keep those declarations in its index instead of dropping them.
    index.extend(own_lines)
    (out_dir / "README.md").write_text("\n".join(index), encoding="utf-8")
    if depth == 0:
        print(f"Wrote index to {out_dir / 'README.md'}")
    return rows


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------


def validate_schema(conn: sqlite3.Connection) -> None:
    for table, required in REQUIRED_COLUMNS.items():
        actual = {row[1] for row in conn.execute(f'PRAGMA table_info("{table}")')}
        if not required <= actual:
            raise ValueError(f"Incompatible documentation schema: {table} lacks {', '.join(sorted(required - actual))}")


def replace_output(generated: Path, output: Path, single: bool) -> None:
    if output == REPO_ROOT or output in REPO_ROOT.parents:
        raise ValueError("Refusing to replace the repository or an ancestor directory")
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix=".signature-output-", dir=output.parent) as tmp:
        staged = Path(tmp) / "new"
        if single:
            shutil.copyfile(generated, staged)
        else:
            shutil.copytree(generated, staged)
        backup = Path(tmp) / "old"
        had_output = output.exists()
        if had_output:
            output.rename(backup)
        try:
            staged.rename(output)
        except OSError:
            if had_output:
                backup.rename(output)
            raise


def extract(args, db: Path) -> int:
    if not db.is_file():
        raise ValueError(f"Database not found at {db}; build docs or supply an existing --db")
    prefix = args.single if args.single is not None else args.root
    single = args.single is not None
    revision = None
    if not single and args.metadata is not None:
        metadata = json.loads(args.metadata.read_text(encoding="utf-8"))
        revision = metadata.get("revision") if isinstance(metadata, dict) else None
        if not isinstance(revision, str) or re.fullmatch(r"[0-9a-f]{40}", revision) is None:
            raise ValueError("Metadata revision must be 40 lowercase hex characters")
    output = args.output.resolve()
    if output == db or output in db.parents:
        raise ValueError("Signature output must not contain the input database")
    with closing(open_readonly(db)) as conn:
        validate_schema(conn)
        if not list_modules(conn, prefix):
            raise ValueError(f"No documented modules match {prefix}")
        with tempfile.TemporaryDirectory(prefix="signature-render-") as tmp:
            generated = Path(tmp) / ("signatures.md" if single else "signatures")
            if single:
                write_single(conn, prefix, generated, args.docstrings)
            else:
                write_split(conn, prefix, generated, args.max_lines, args.docstrings, revision=revision)
            replace_output(generated, output, single)
            print(f"Updated signature output at {output}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Extract Lean declaration signatures from docgen SQLite DB."
    )
    parser.add_argument(
        "--single",
        metavar="MODULE",
        default=None,
        help="Extract a single dotted module prefix to one file. "
        "E.g. --single MathEconLib.Probability. Default (when omitted): split mode.",
    )
    parser.add_argument(
        "-o",
        "--output",
        type=Path,
        required=True,
        help="Output path. In single mode: target .md file. In split mode: target directory.",
    )
    parser.add_argument(
        "--root",
        default="MathEconLib",
        help="Root module for split mode (default: MathEconLib). Top-level submodules become files.",
    )
    parser.add_argument(
        "-d", "--docstrings", action="store_true", help="Include docstrings in the output"
    )
    parser.add_argument(
        "--max-lines",
        type=int,
        default=2000,
        help="In split mode, recursively break up any module whose flat rendering would "
        "exceed this many lines (default: 2000). Set to 0 to disable recursive splitting.",
    )
    parser.add_argument("--metadata", type=Path, help="Build metadata.json with the source revision (ignored in single mode)")
    parser.add_argument("--db", type=Path, help="Existing api-docs.db (requires --no-build)")
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Use an existing --db instead of building temporary documentation",
    )
    args = parser.parse_args()
    if args.no_build != (args.db is not None):
        parser.error("Use --no-build and --db together, or omit both to build documentation")
    if args.max_lines < 0:
        parser.error("--max-lines must be nonnegative")
    try:
        if args.no_build:
            return extract(args, args.db.resolve())
        with tempfile.TemporaryDirectory(prefix="signature-database-") as tmp:
            output = Path(tmp)
            build_docs(output)
            return extract(args, output / "api-docs.db")
    except (OSError, ValueError, sqlite3.Error, subprocess.CalledProcessError) as error:
        print(f"Error: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
