# cairn_json: build, check and fuzz. See README.md.
export PATH := $(HOME)/.elan/bin:$(PATH)

.PHONY: build lint audit kernel fuzz fuzz-quick check clean

build:
	cd lean && lake build CairnJson CairnJsonProofs

# Constructs that bypass the kernel, run unchecked code or aren't total (cairn's AGENTS.md,
# "Writing Lean"), and `import Lean` in the library apps link.
lint:
	@! grep -rnE 'implemented_by|@\[extern|skipKernelTC|native_decide|bv_decide|^\s*(private |public )?(partial|unsafe) def|\bsorry\b|^\s*axiom ' \
	  lean/CairnJson lean/CairnJson.lean lean/CairnJsonProofs lean/CairnJsonProofs.lean lean/Fuzz \
	  || (echo "lint: forbidden construct (AGENTS.md, Rules)"; exit 1)
	@! grep -rnE '^\s*(public )?import Lean' lean/CairnJson lean/CairnJson.lean \
	  || (echo "lint: CairnJson must not import Lean"; exit 1)

# Every theorem depends on propext, Classical.choice and Quot.sound at most (cairn's `audit`).
audit: build
	cd lean && lake exe audit CairnJson CairnJsonProofs

# Replay every declaration through the kernel.
kernel: build
	cd lean && lake check --inadvisably-no-sandbox

build/jsonfuzz-driver: fuzz/main.swift
	@mkdir -p build
	swiftc -O fuzz/main.swift -o $@

# The trusted fuzz check against Foundation's JSONSerialization (docs/trusted.md).
fuzz: build/jsonfuzz-driver
	cd lean && lake build jsonfuzz
	build/jsonfuzz-driver lean/.lake/build/bin/jsonfuzz 100000 $${SEED:-1}

fuzz-quick: build/jsonfuzz-driver
	cd lean && lake build jsonfuzz
	build/jsonfuzz-driver lean/.lake/build/bin/jsonfuzz 5000 $${SEED:-1}

check: lint build audit kernel fuzz-quick

clean:
	rm -rf build lean/.lake/build
