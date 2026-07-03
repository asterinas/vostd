.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	ostd \

.PHONY: all verify $(VERIFICATION_TARGETS) fmt clean verus verus-upgrade

$(VERIFICATION_TARGETS):
	cargo dv verify --targets $@

all: verify

verify:
	cargo dv verify --targets $(VERIFICATION_TARGETS)

fmt:
	cargo dv fmt

build:
	cargo dv build

doc: build
	cargo dv doc --target ostd

verus:
	cargo dv bootstrap

verus-upgrade:
	cargo dv bootstrap --upgrade

clean:
	cargo clean
	rm -rf doc
