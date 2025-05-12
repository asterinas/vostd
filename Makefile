.DEFAULT_GOAL := all
.PHONY: lock-protocol

# List of verification targets
VERIFICATION_TARGETS := \
	fvt1-mem-region-init \
	fvt3-page-acquisition-safety \
	fvt4-into-from-raw \
	fvt5-lifecycle-safety \
	fvt6-vmreader-and-vmwriter \
	fvt10-pt-cursor-navigation \
	fvt11-pt-cursor-guards \
	fvt13-vmspace-unmap-safety \
	lock-protocol

# Compile-only targets
COMPILE_TARGETS := vstd_extra aster_common

# Pattern rule for individual FVT targets
fvt%:
	cargo xtask verify --targets $(filter fvt$*-%, $(VERIFICATION_TARGETS))

lock-protocol:
	cargo xtask verify --targets lock-protocol

fmt:
	cargo xtask fmt

all: compile verify

compile:
	@for target in $(COMPILE_TARGETS); do \
		cargo xtask compile --targets $$target; \
	done

verify:
	@for target in $(VERIFICATION_TARGETS); do \
		cargo xtask verify --targets $$target; \
	done

clean:
	cargo clean
