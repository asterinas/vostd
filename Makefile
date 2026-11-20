.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	ostd \

RUST_TARGETS := \
	x86_64-unknown-none \
	riscv64imac-unknown-none-elf \
	loongarch64-unknown-none-softfloat \

.PHONY: all verify $(VERIFICATION_TARGETS) verify-x86 verify-riscv verify-loongarch \
	verify-bzimage \
	fmt build doc clean verus verus-upgrade

$(VERIFICATION_TARGETS):
	cargo dv verify --package $@

all: verify

verify:
	cargo dv verify --package $(VERIFICATION_TARGETS)

verify-%:
	cargo dv verify --package $(VERIFICATION_TARGETS) --target $*

# Short aliases.
verify-x86: verify-x86_64-unknown-none
verify-riscv: verify-riscv64imac-unknown-none-elf
verify-loongarch: verify-loongarch64-unknown-none-softfloat

verify-bzimage:
	cargo dv verify --package linux-bzimage-builder --target x86_64-unknown-linux-gnu
	PAYLOAD_FILE=/dev/null cargo dv verify --package linux-bzimage-setup --target x86_64-unknown-none

fmt:
	cargo fmt --manifest-path dv/Cargo.toml --all
	cargo dv fmt

build:
	cargo dv build

doc:
	cargo dv build --package ostd -- --no-verify
	cargo dv doc --package ostd

verus:
	cargo dv bootstrap

verus-upgrade:
	cargo dv bootstrap --upgrade

clean:
	cargo clean
	rm -rf doc
