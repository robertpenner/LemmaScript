#!/usr/bin/env bash
# Runs the Dafny number-encoding spike and writes everything REPORT.md cites
# into results/. Each corpus file gets one isolated run
# (--isolate-assertions, per-batch CSV log in results/verify/*.csv) and one
# whole-file run per seed (results/seeds/). Seeds go through Boogie's
# -randomSeed option because 4.11 `dafny verify` has no --random-seed.
#
#   DAFNY_FP=/path/to/nightly/dafny spikes/dafny-number-encodings/run.sh
#
# Environment:
#   DAFNY      pinned Dafny 4.11.0 for Encodings A and B (default: dafny)
#   DAFNY_FP   Dafny nightly with fp64 for Encoding C and the repros.
#              Example used for the recorded results:
#              .../dafny-nightly/dafny/dafny (4.11.1+a8692441e735...).
#              When unset, Encoding C, the repros and the C js build are
#              skipped and the skip is recorded in results/.
#   LIMIT      --verification-time-limit in seconds (default 30)
#   SEEDS      seeds for the whole-file timing runs (default "1 2 3")
#   NODE_PATH  where node finds bignumber.js for the -t js runs
#              (default: the repository's node_modules)
#   VECTORS    path to the fork #23 math-special-values.json. When set, the
#              vectors section turns a sample of its Math.min/max/trunc/round
#              records into lemmas (vectors/gen-dfy.mjs) and verifies them
#              against B_lib and C_lib. When unset, the section is skipped
#              and the skip is recorded in results/vectors.csv.
#   SECTIONS   which parts to run (default "verify repro js vectors"). A partial
#              run regenerates only the named parts of results/ and
#              versions.txt.
#
# Bash 3.2 compatible. Exit codes of individual tools are recorded, not
# acted on, so the script keeps going past failures and timeouts.

set -u

HERE=$(cd "$(dirname "$0")" && pwd)
PINNED=${DAFNY:-dafny}
FP=${DAFNY_FP:-}
LIMIT=${LIMIT:-30}
SEEDS=${SEEDS:-"1 2 3"}
SECTIONS=${SECTIONS:-"verify repro js vectors"}
VEC=${VECTORS:-}
export NODE_PATH=${NODE_PATH:-$(cd "$HERE/../.." && pwd)/node_modules}

RES=$HERE/results
BUILD=$HERE/.build
has() { case " $SECTIONS " in *" $1 "*) return 0 ;; *) return 1 ;; esac; }
rm -rf "$BUILD" "$RES/versions.txt"
has verify && rm -rf "$RES/verify" "$RES/seeds" "$RES/summary.csv"
has repro && rm -rf "$RES/repro" "$RES/repro.csv"
has js && rm -rf "$RES/js" "$RES/js.csv"
has vectors && rm -rf "$RES/vectors" "$RES/vectors.csv"
mkdir -p "$RES/verify" "$RES/seeds" "$RES/repro" "$RES/js" "$RES/vectors" "$BUILD"
# The checkout's package.json declares "type": "module", but Dafny emits
# CommonJS, so mark the build directory as CommonJS for node.
echo '{ "type": "commonjs" }' > "$BUILD/package.json"

now() { perl -MTime::HiRes=time -e 'printf "%.2f", time'; }
elapsed() { perl -e "printf '%.2f', $2 - $1"; }

# Prints "verified,errors,timeouts" from a Dafny output file, or "-,-,-"
# when there is no summary line (resolution failure or crash).
counts() {
  local line
  line=$(grep -E 'Dafny program verifier finished with' "$1" | tail -1)
  if [ -z "$line" ]; then echo "-,-,-"; return; fi
  local v e t
  v=$(echo "$line" | sed -E 's/.* ([0-9]+) verified.*/\1/')
  e=$(echo "$line" | sed -E 's/.* ([0-9]+) errors?.*/\1/')
  if echo "$line" | grep -q 'time out'; then
    t=$(echo "$line" | sed -E 's/.* ([0-9]+) time outs?.*/\1/')
  else
    t=0
  fi
  echo "$v,$e,$t"
}

tagcount() { grep -c -- "$1" "$2" | tr -d ' '; }

dafny_dir() {
  local p r
  p=$(command -v "$1")
  r=$(readlink -f "$p" 2>/dev/null || echo "$p")
  dirname "$r"
}

record_versions() {
  local label=$1 bin=$2 dir out
  dir=$(dafny_dir "$bin")
  out=$RES/versions.txt
  {
    echo "[$label]"
    echo "binary: $(basename "$dir")/$(basename "$bin")"
    echo "dafny --version: $("$bin" --version 2>&1 | head -1)"
    echo "boogie (DafnyDriver.deps.json): $(grep -o '"Boogie.ExecutionEngine/[0-9.]*"' "$dir/DafnyDriver.deps.json" | head -1 | tr -d '"')"
    echo "bundled z3: $(ls "$dir/z3/bin" | tr '\n' ' ')"
    printf 'lemma T() { assert 1 + 1 == 2; }\n' > "$BUILD/tiny.dfy"
    "$bin" verify --boogie -trace "$BUILD/tiny.dfy" > "$BUILD/trace-$label.out" 2>&1
    echo "default prover (verify --boogie -trace): $(grep -i 'Using prover' "$BUILD/trace-$label.out" | head -1 | sed -E 's#.*/##')"
    echo
  } >> "$out"
}

{
  echo "date: $(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  echo "host: $(uname -sm), $(sysctl -n hw.ncpu 2>/dev/null) logical cpus"
  echo "node: $(node --version 2>&1)"
  echo "verification time limit: ${LIMIT}s"
  echo "seeds: $SEEDS"
  echo "sections: $SECTIONS"
  if [ -n "$VEC" ]; then
    echo "vectors: $(basename "$VEC") sha256 $(shasum -a 256 "$VEC" | cut -d' ' -f1)"
  fi
  echo
} > "$RES/versions.txt"
record_versions pinned "$PINNED"
if [ -n "$FP" ]; then
  record_versions nightly "$FP"
else
  echo "[nightly] skipped: DAFNY_FP unset" >> "$RES/versions.txt"
fi

# ---------------------------------------------------------------- corpus

if has verify; then
echo "encoding,file,mode,exit,verified,errors,timeouts,seconds,manual_tags,lemma_tags" > "$RES/summary.csv"

run_corpus_file() {
  local enc=$1 bin=$2 name=$3 mode=$4
  shift 4
  local file=$HERE/corpus/$name.dfy lib=$HERE/corpus/${enc}_lib.dfy
  local libargs="" out t0 t1 ec
  if [ "$name" != "${enc}_lib" ]; then libargs="--library $lib"; fi
  if [ "$mode" = isolated ]; then
    out=$RES/verify/$name.out
  else
    out=$RES/seeds/$name.$mode.out
  fi
  t0=$(now)
  # shellcheck disable=SC2086
  (cd "$HERE" && "$bin" verify --allow-warnings --verification-time-limit "$LIMIT" $libargs "$@" "corpus/$name.dfy") > "$out" 2>&1
  ec=$?
  t1=$(now)
  echo "$enc,$name,$mode,$ec,$(counts "$out"),$(elapsed "$t0" "$t1"),$(tagcount '@manual' "$file"),$(tagcount '@lemma' "$file")" >> "$RES/summary.csv"
  echo "  $name $mode exit=$ec $(counts "$out")"
}

run_encoding() {
  local enc=$1 bin=$2
  shift 2
  local name seed
  for name in "$@"; do
    run_corpus_file "$enc" "$bin" "$name" isolated --isolate-assertions \
      --log-format "csv;LogFileName=$RES/verify/$name.csv"
    for seed in $SEEDS; do
      run_corpus_file "$enc" "$bin" "$name" "seed$seed" --boogie "-randomSeed:$seed"
    done
  done
}

echo "Encoding A (pinned)"
run_encoding A "$PINNED" A_lib A_safeint A_clamp A_bitwise
echo "Encoding B (pinned)"
run_encoding B "$PINNED" B_lib B_safeint B_clamp B_signedzero B_bitwise B_lerp
if [ -n "$FP" ]; then
  echo "Encoding C (nightly)"
  run_encoding C "$FP" C_lib C_safeint C_clamp C_signedzero C_bitwise C_lerp
else
  echo "C,skipped,DAFNY_FP unset,,,,,,," >> "$RES/summary.csv"
fi
fi

# ---------------------------------------------------------------- repros

if has repro; then
echo "file,toolchain,solver,exit,verified,errors,timeouts,seconds" > "$RES/repro.csv"

run_repro() {
  local name=$1 label=$2 bin=$3 solver=$4
  local out=$RES/repro/$name.$label.out t0 t1 ec
  shift 4
  t0=$(now)
  (cd "$HERE" && "$bin" verify --allow-warnings --isolate-assertions --verification-time-limit "$LIMIT" "$@" "repro/$name.dfy") > "$BUILD/repro.raw" 2>&1
  ec=$?
  t1=$(now)
  # Crashes print long .NET stack traces; keep the head, which names the
  # exception and the throwing method.
  head -40 "$BUILD/repro.raw" > "$out"
  echo "$name,$label,$solver,$ec,$(counts "$BUILD/repro.raw"),$(elapsed "$t0" "$t1")" >> "$RES/repro.csv"
  echo "  $name $label exit=$ec $(counts "$BUILD/repro.raw")"
}

echo "Repros"
run_repro P01_PinnedNoFp64 pinned "$PINNED" default
if [ -n "$FP" ]; then
  fpdir=$(dafny_dir "$FP")
  for f in "$HERE"/repro/R*.dfy; do
    name=$(basename "$f" .dfy)
    run_repro "$name" nightly-z3-4.16.0 "$FP" z3-4.16.0 --solver-path "$fpdir/z3/bin/z3-4.16.0"
    run_repro "$name" nightly-z3-4.12.1 "$FP" z3-4.12.1 --solver-path "$fpdir/z3/bin/z3-4.12.1"
  done
else
  echo "R*,nightly,skipped,DAFNY_FP unset,,,," >> "$RES/repro.csv"
fi
fi

# ---------------------------------------------------------------- -t js

if has js; then
echo "program,toolchain,build_exit,run_exit" > "$RES/js.csv"

run_js() {
  local prog=$1 label=$2 bin=$3
  shift 3
  local bec rec=-
  (cd "$HERE" && "$bin" build -t js --no-verify --allow-warnings --output "$BUILD/$prog" "js/$prog.dfy" "$@") > "$BUILD/$prog.build.raw" 2>&1
  bec=$?
  head -20 "$BUILD/$prog.build.raw" > "$RES/js/$prog.build.out"
  if [ "$bec" -eq 0 ] && [ -f "$BUILD/$prog.js" ]; then
    (cd "$BUILD" && node "$prog.js") > "$BUILD/$prog.run.raw" 2>&1
    rec=$?
    head -20 "$BUILD/$prog.run.raw" > "$RES/js/$prog.run.out"
  fi
  echo "$prog,$label,$bec,$rec" >> "$RES/js.csv"
  echo "  $prog build=$bec run=$rec"
}

echo "-t js"
run_js A_main pinned "$PINNED" corpus/A_lib.dfy corpus/A_safeint.dfy corpus/A_clamp.dfy
run_js B_main pinned "$PINNED" corpus/B_lib.dfy corpus/B_clamp.dfy corpus/B_lerp.dfy
if [ -n "$FP" ]; then
  run_js C_main nightly "$FP" corpus/C_lib.dfy corpus/C_clamp.dfy corpus/C_lerp.dfy
  run_js C_min nightly "$FP"
  run_js C_nan nightly "$FP"
else
  echo "C_*,nightly,skipped,skipped" >> "$RES/js.csv"
fi
fi

# --------------------------------------------------------------- vectors

if has vectors; then
echo "encoding,toolchain,exit,lemmas,verified,errors,timeouts,seconds" > "$RES/vectors.csv"

run_vectors() {
  local enc=$1 label=$2 bin=$3 file out t0 t1 ec
  file=$RES/vectors/${enc}_vectors.dfy
  out=$RES/vectors/${enc}_vectors.out
  t0=$(now)
  (cd "$HERE" && "$bin" verify --allow-warnings --isolate-assertions --verification-time-limit "$LIMIT" \
    --log-format "csv;LogFileName=$RES/vectors/${enc}_vectors.csv" \
    --library "corpus/${enc}_lib.dfy" "$file") > "$out" 2>&1
  ec=$?
  t1=$(now)
  echo "$enc,$label,$ec,$(tagcount '^lemma' "$file"),$(counts "$out"),$(elapsed "$t0" "$t1")" >> "$RES/vectors.csv"
  echo "  ${enc}_vectors exit=$ec $(counts "$out")"
}

echo "Vectors"
if [ -n "$VEC" ]; then
  node "$HERE/vectors/gen-dfy.mjs" "$VEC" "$RES/vectors"
  run_vectors B pinned "$PINNED"
  if [ -n "$FP" ]; then
    run_vectors C nightly "$FP"
  else
    echo "C,nightly,skipped,,,,," >> "$RES/vectors.csv"
  fi
else
  echo "B+C,skipped,VECTORS unset,,,,," >> "$RES/vectors.csv"
fi
fi

echo "done: $RES"
