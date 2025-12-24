.DEFAULT_GOAL := all

VERIFICATION_TARGETS := \
	ostd \

# Disabled:
# 	demo

.PHONY: all verify $(VERIFICATION_TARGETS) fmt clean

$(VERIFICATION_TARGETS):
	mkdir -p target
	cargo dv verify --targets $@

all: verify

verify:
	mkdir -p target
	cargo dv verify --targets $(VERIFICATION_TARGETS)

fmt:
	cargo dv fmt

clean:
	cargo clean
