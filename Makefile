.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	ostd \

RUST_TARGETS := \
	x86_64-unknown-none \
	riscv64imac-unknown-none-elf \
	loongarch64-unknown-none-softfloat \

.PHONY: all verify $(VERIFICATION_TARGETS) verify-x86 verify-riscv verify-loongarch \
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

fmt:
	cargo dv fmt

build:
	cargo dv build

doc:
	cargo dv build -- --no-verify
	cargo dv doc --package ostd

verus:
	cargo dv bootstrap

verus-upgrade:
	cargo dv bootstrap --upgrade

clean:
	cargo clean
	rm -rf doc
