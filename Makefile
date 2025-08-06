.DEFAULT_GOAL := all
.PHONY: lock-protocol all compile verify verify-parallel clean fmt

VERIFICATION_TARGETS := \
	fvt1-mem-region-init \
	fvt3-page-acquisition-safety \
	fvt4-into-from-raw \
	fvt6-vmreader-and-vmwriter \
	fvt10-pt-cursor-navigation \
	fvt11-pt-cursor-guards \
	lock-protocol

# Disabled:
# fvt5-lifecycle-safety
# fvt13-vmspace-unmap-safety 

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
	cargo xtask compile --targets $(COMPILE_TARGETS)

verify:
	cargo xtask verify --targets $(VERIFICATION_TARGETS) $(if $(VOSTD_VERIFY_PARALLEL),--parallel)

verify-parallel:
	VOSTD_VERIFY_PARALLEL=1 $(MAKE) verify

clean:
	cargo clean