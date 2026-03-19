#!/bin/bash
# Stress test suite: one medium-hard problem per problem type (18 total)
# All run in parallel for speed.

set -uo pipefail
cd "$(dirname "$0")"
export $(cat .env | xargs)

ROUNDS=5
TIMEOUT=60000
RESULTS_DIR="/tmp/catlab-test-results"
REFLECT_DIR="/tmp/catlab-test-reflections"
rm -rf "$RESULTS_DIR" "$REFLECT_DIR"
mkdir -p "$RESULTS_DIR" "$REFLECT_DIR"

run_test() {
  local id="$1"
  local label="$2"
  shift 2
  local outfile="$RESULTS_DIR/$id.txt"
  local reflectfile="$REFLECT_DIR/$id.txt"

  output=$(node dist/index.js "$@" --rounds "$ROUNDS" --timeout "$TIMEOUT" --reflect 2>&1 || true)

  status=$(echo "$output" | grep -E '(✅|❌|EXHAUSTED|Fatal)' | head -1)
  rounds=$(echo "$output" | sed -n 's/.*round \([0-9]*\)\/.*/\1/p' | tail -1)

  # Capture reflection output
  reflection=$(echo "$output" | sed -n '/\[solver:REFLECT\] Suggestions:/,/^\[/{ /\[solver:REFLECT\] Suggestions:/d; /^\[/d; p; }')
  if [ -n "$reflection" ]; then
    echo "── $label (round $rounds) ──" > "$reflectfile"
    echo "$reflection" >> "$reflectfile"
  fi

  if echo "$status" | grep -q '✅'; then
    echo "✅ $label (round $rounds)" > "$outfile"
  else
    reason=$(echo "$status" | head -c 120)
    echo "❌ $label — $reason" > "$outfile"
  fi
}

echo "Launching 18 tests in parallel..."

run_test 01 "Inverse: Ring opposite" Ring opposite &
run_test 02 "Fixed-point: AbelianGroup opposite" --problem fixed-point --target AbelianGroup --op opposite &
run_test 03 "Pushout complement: Monoid→Group" --problem pushout-complement --base Monoid --target Group &
run_test 04 "Pullback complement: Monoid→Group" --problem pullback-complement --base Monoid --target Group &
run_test 05 "Extension: Group+commutative" --problem extension --base Group --property commutative &
run_test 06 "Interpolation: Monoid→Group" --problem interpolation --base Monoid --target Group &
run_test 07 "Simplification: Group" --problem simplify --target Group &
run_test 08 "Model finding: Ring" --problem model-finding --target Ring &
run_test 09 "Synthesis: Group M→M" --problem synthesis --base Group --source M --target M &
run_test 10 "Quotient: Ring+commutative" --problem quotient --base Ring --property commutative &
run_test 11 "Relaxation: Group drop_inverses" --problem relax --target Group --property drop_inverses &
run_test 12 "Sub-object: Ring additive" --problem subobject --target Ring --property additive_only &
run_test 13 "Decomposition: Ring" --problem decompose --target Ring &
run_test 14 "Catalyst: Group→Group" --problem catalyst --source Group --target Group &
run_test 15 "Compose: inverse+fixed-point Group" --problem compose --constraints "inverse:Group:opposite+fixed-point:Group:opposite" &
run_test 16 "Multi-objective: Group opposite+identity" --problem multi --objectives "Group:opposite,Group:identity" &
run_test 17 "Factorization: Ring" --problem factorization --target Ring &
run_test 18 "Optimization: Group opposite minimize" --problem optimization --target Group --op opposite --property "minimize generators" &

echo "Waiting for all 18 tests..."
wait

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "RESULTS:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"

pass=0
fail=0
for f in $(ls "$RESULTS_DIR"/*.txt | sort); do
  result=$(cat "$f")
  echo "  $result"
  if echo "$result" | grep -q '✅'; then ((pass++)); else ((fail++)); fi
done

echo ""
echo "TOTAL: $pass pass, $fail fail out of 18"

echo ""
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
echo "REFLECTIONS:"
echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
for f in $(ls "$REFLECT_DIR"/*.txt 2>/dev/null | sort); do
  cat "$f"
  echo ""
done
