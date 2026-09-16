#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT

lake build Challenge Solution
lake env lean -DwarningAsError=true Solution.lean
# Match Palomar's direct compilation: no Lake -D options, and publish the
# result under a different module name. Deliberate placeholders are expected.
mkdir -p "$work/PalomarCanonicalCheck"
lake env lean -o "$work/PalomarCanonicalCheck/Challenge.olean" Challenge.lean
LEAN_PATH="$work${LEAN_PATH:+:$LEAN_PATH}" lake env lean -DwarningAsError=true \
  --run Palomar/CheckStatements.lean PalomarCanonicalCheck.Challenge

python3 - "$work" <<'PY'
import json, pathlib, re, sys
root = pathlib.Path('.')
config = json.loads((root / 'comparator.json').read_text())
assert set(config['permitted_axioms']) == {'propext', 'Quot.sound', 'Classical.choice'}
assert config['enable_nanoda'] is True
assert config['definition_names'] == []
challenge = (root / 'Challenge.lean').read_text()
solution = (root / 'Solution.lean').read_text()
assert len(challenge.encode()) <= 100 * 1024 and len(challenge.splitlines()) <= 1000
assert all((line == 'import Mathlib' or line.startswith('import Mathlib.')) for line in challenge.splitlines() if line.startswith('import '))
assert 'import Challenge' not in solution
declarations = re.findall(r'^theorem (\w+)\b(.*?)(?=^theorem |\Z)', challenge, re.M | re.S)
assert {name for name, body in declarations if 'by sorry' in body} == {
    n.rsplit('.', 1)[1] for n in config['theorem_names']}
assert len(re.findall(r'\bsorry\b', '\n'.join(
    line for line in challenge.splitlines() if line.strip() == 'by sorry'))) == len(config['theorem_names'])
assert len(config['theorem_names']) == len(set(config['theorem_names']))
for name in config['theorem_names']:
    short = name.rsplit('.', 1)[1]
    pattern = rf'theorem {re.escape(short)}\b(.*?) :=\n'
    left = re.search(pattern, challenge, re.S)
    right = re.search(pattern, solution, re.S)
    assert left and right and left.group(1) == right.group(1), name
path = pathlib.Path(sys.argv[1]) / 'Audit.lean'
path.write_text('import Solution\n' + ''.join('#print axioms ' + n + '\n' for n in config['theorem_names']))
PY
lake env lean "$work/Audit.lean" > "$work/axioms.txt"
cat "$work/axioms.txt"
python3 - "$work/axioms.txt" <<'PY'
import json, pathlib, re, sys
text = pathlib.Path(sys.argv[1]).read_text()
config = json.loads(pathlib.Path('comparator.json').read_text())
for name in config['theorem_names']:
    match = re.search(re.escape("'" + name + "' depends on axioms:") + r'\s*\[([^]]*)\]', text)
    assert match, f'Missing axiom audit for {name}'
    axioms = {a.strip() for a in match.group(1).split(',') if a.strip()}
    assert axioms <= set(config['permitted_axioms']), (name, axioms)
print('Local Palomar checks passed; Comparator/NanoDa verification remains separate.')
PY
