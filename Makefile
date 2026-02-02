.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	ostd \

# Disabled:
# 	demo

.PHONY: all verify $(VERIFICATION_TARGETS) fmt clean

$(VERIFICATION_TARGETS):
	cargo dv verify --targets $@

all: verify

verify:
	cargo dv verify --targets $(VERIFICATION_TARGETS)

fmt:
	cargo dv fmt

doc: verify
	cargo dv doc --target ostd

clean:
	cargo clean
	rm -rf doc
