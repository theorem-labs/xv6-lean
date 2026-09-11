#!/usr/bin/env python3
"""Report supplied Rocq Print logs; never invokes a compiler or installs packages.

Names/types are pretty-printed text, not canonical kernel identifiers/terms.
Raw sections and source locations are retained so inferred boundaries are reviewable.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import re
import shlex
from pathlib import Path

ROOTS = [
    ("SystemAdequacy", "xv6_power_adequacy_xv6Σ", "conditional_invariant"),
    ("SystemAdequacy", "xv6_fs_adequacy_xv6Σ", "concrete_initial_state"),
    ("SystemAdequacy", "xv6_trace_adequacy_xv6Σ", "conditional_trace_resources"),
    ("SystemAdequacy", "xv6_obs_wf_xv6Σ", "concrete_initial_state"),
    ("SystemUartAccepted", "xv6_out_accepted_xv6Σ", "concrete_initial_state"),
    ("SystemUartAccepted", "xv6_out_accepted_from_xv6Σ", "conditional_located_receipt_residue"),
]
HEADERS = ["Transparent constants:", "Section Variables:", "Axioms:",
           "Opaque constants:", "Theory:"]
CLOSED = "Closed under the global context"
ENTRY = re.compile(r"^([\w][\w'.]*)\s+:(?:\s|$)", re.UNICODE)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def parse_log(raw: str) -> list[dict]:
    """Split ordered printer sections; report boundaries inferred from rank resets.

    Rocq emits sections in HEADERS order, omitting empty sections. A repeated or
    lower-ranked header starts another command response. There are no command
    delimiters in these original logs. Closed responses each form one report.
    """
    reports: list[dict] = []
    report: dict | None = None
    section: dict | None = None
    rank = -1
    for number, line in enumerate(raw.splitlines(), 1):
        if line == CLOSED:
            reports.append({"closed_message": True, "start_line": number, "sections": []})
            report, section, rank = None, None, -1
        elif line in HEADERS:
            current = HEADERS.index(line)
            if report is None or current <= rank:
                report = {"closed_message": False, "start_line": number, "sections": []}
                reports.append(report)
            section = {"category": line[:-1], "start_line": number, "raw_lines": []}
            report["sections"].append(section)
            rank = current
        elif section is not None:
            section["raw_lines"].append(line)
        elif line.strip():
            raise ValueError(f"unexpected text outside printer section at line {number}: {line}")
    for item in reports:
        for section in item["sections"]:
            entries = []
            for offset, line in enumerate(section["raw_lines"], 1):
                match = ENTRY.match(line)
                if match:
                    entries.append({"printed_name": match.group(1),
                                    "line": section["start_line"] + offset})
            section["name_candidates"] = entries
            section["name_candidate_count"] = len(entries)
            # Keep the exact rendered text: this is deliberately not a Rocq term parser.
            section["raw_text"] = "\n".join(section.pop("raw_lines"))
    return reports


def inventory(source: Path) -> list[dict]:
    result = []
    for module, name, scope in ROOTS:
        path = source / "iris" / (module + ".v")
        data = path.read_bytes()
        text = data.decode()
        start = re.search(r"^Corollary " + re.escape(name) + r"\b", text, re.MULTILINE)
        if start is None:
            raise ValueError(f"missing source root {module}.{name}")
        proof = re.search(r"^Proof\.", text[start.start():], re.MULTILINE)
        if proof is None:
            raise ValueError(f"missing proof boundary {module}.{name}")
        statement = text[start.start():start.start() + proof.start()].rstrip()
        if not statement.endswith("."):
            raise ValueError(f"unterminated statement {name}")
        result.append({"root": module + "." + name, "source_path": "iris/" + path.name,
                       "line": text[:start.start()].count("\n") + 1, "scope": scope,
                       "source_file_sha256": digest(data), "statement": statement,
                       "statement_sha256": digest(statement.encode())})
    return result


def load_records(text: str) -> list[dict]:
    if text.lstrip().startswith("["):
        records = json.loads(text)
    else:
        records = [json.loads(line) for line in text.splitlines() if line.strip()]
    if not isinstance(records, list):
        raise ValueError("audit manifest must be a JSON array or JSONL records")
    return records


def generate(manifest: Path, source: Path, graph: Path | None, require_complete: bool) -> dict:
    expected = {(module + "." + name, kind) for module, name, _ in ROOTS
                for kind in ["statement_dependencies", "proof_assumptions"]}
    seen = set()
    records = []
    manifest_data = manifest.read_bytes()
    for record in load_records(manifest_data.decode()):
        key = (record["root"], record["kind"])
        if key not in expected or key in seen:
            raise ValueError(f"unexpected or duplicate audit record {key}")
        if record["exit_code"] != 0:
            raise ValueError(f"unsuccessful audit {key}")
        seen.add(key)
        path = Path(record["log"])
        if not path.is_absolute():
            path = manifest.parent / path
        raw = path.read_bytes()
        if digest(raw) != record["sha256"]:
            raise ValueError(f"raw log hash mismatch {path}")
        reports = parse_log(raw.decode())
        commands = (["Print All Dependencies statement_seed", "Print Assumptions statement_seed"]
                    if record["kind"] == "statement_dependencies"
                    else ["Print Assumptions theorem_root"])
        if len(reports) != len(commands):
            raise ValueError(f"expected {len(commands)} reports in {path}, found {len(reports)}")
        for command, report in zip(commands, reports):
            report["command"] = command
        records.append({**record, "reports": reports})
    if require_complete and seen != expected:
        raise ValueError(f"missing audit records: {sorted(expected - seen)}")
    result = {
        "schema_version": 1,
        "kind": "Rocq pretty-printed constant/assumption report, not a declaration graph",
        "manifest": str(manifest), "manifest_sha256": digest(manifest_data),
        "complete_audit_matrix": seen == expected, "missing_records": sorted(expected - seen),
        "interpretation": {
            "printed_names_are_canonical": False,
            "constructor_inventory_included": False,
            "constant_type_and_body_closure_certified": False,
            "semantic_correspondence_to_lean_certified": False,
            "statement_seed": "body is elaborated theorem type; root proof body is not the seed",
            "assumptions": "printer frontier includes primitives; categories retained without relabeling",
            "boundaries": "inferred from Rocq 9.0.1 printer section order; raw text retained",
            "name_candidates": "column-zero name-colon rendering; not a kernel identifier parser",
        },
        "theorem_roots": inventory(source), "audit_records": sorted(records, key=lambda x: (x["root"], x["kind"])),
    }
    if graph:
        data = graph.read_bytes()
        supplied = json.loads(data)
        normalized = dict(supplied)
        normalized.pop("all_dependencies_active", None)
        active = set()
        projects = []
        for directory in ["iris", "model-xv6iris", "kernel-rocq", "user-rocq"]:
            project = source / directory / "_CoqProject"
            project_data = project.read_bytes()
            files = [directory + "/" + token for token in
                     shlex.split(project_data.decode(), comments=True) if token.endswith(".v")]
            active.update(files)
            projects.append({"path": directory + "/_CoqProject",
                             "sha256": digest(project_data), "listed_source_count": len(files)})
        counts = {}
        union = set()
        for seed in supplied["seeds"]:
            reached, work = set(), [seed]
            while work:
                node = work.pop()
                if node in reached:
                    continue
                reached.add(node)
                work.extend(supplied["module_edges"][node])
            counts[seed] = len(reached)
            union.update(reached)
        if counts != supplied["per_root_counts"] or union != set(supplied["module_union"]):
            raise ValueError("supplied module graph counts/union disagree with its edges")
        missing = sorted(node.removesuffix(".vo") + ".v" for node in union
                         if node.removesuffix(".vo") + ".v" not in active)
        normalized["reached_local_modules_listed_in_active_projects"] = not missing
        result["compiler_import_graph"] = {
            "path": str(graph), "sha256": digest(data), "normalized_report": normalized,
            "active_projects": projects, "reached_sources_missing_from_projects": missing,
            "interpretation": "local module imports only; external libraries remain required; "
                              "active project membership is not declaration/proof use",
        }
    return result


def self_test() -> None:
    raw = "Transparent constants:\nA.x :\nforall T, T -> T\nAxioms:\nP : Prop\nOpaque constants:\nM.p : P\nAxioms:\nP : Prop\n"
    reports = parse_log(raw)
    assert len(reports) == 2
    assert reports[0]["sections"][0]["name_candidates"] == [{"printed_name": "A.x", "line": 2}]
    assert reports[0]["sections"][0]["raw_text"] == "A.x :\nforall T, T -> T"
    assert len(parse_log(CLOSED + "\n" + CLOSED)) == 2
    assert len(parse_log("Axioms:\nP : Prop\nAxioms:\nP : Prop")) == 2
    assert parse_log("Theory:\nSet is impredicative")[0]["sections"][0]["name_candidates"] == []
    try:
        parse_log("Error: failed command")
    except ValueError:
        pass
    else:
        raise AssertionError("must reject diagnostics outside a report")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--import-graph", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--require-complete", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
    if args.manifest:
        if args.source_root is None or args.output is None:
            parser.error("--manifest requires --source-root and --output")
        result = generate(args.manifest, args.source_root, args.import_graph, args.require_complete)
        args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
        print(f"wrote {len(result['audit_records'])}/12 audit records; complete={result['complete_audit_matrix']}")
    elif not args.self_test:
        parser.error("supply --manifest or --self-test")


if __name__ == "__main__":
    main()
