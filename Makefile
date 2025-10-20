.DEFAULT_GOAL := all
.PHONY: lock-protocol-rcu all compile verify verify-parallel clean fmt

VERIFICATION_TARGETS := \
	lock-protocol-rcu

# Disabled:
# fvt5-lifecycle-safety
# fvt13-vmspace-unmap-safety 

COMPILE_TARGETS := vstd_extra aster_common

# Pattern rule for individual FVT targets
fvt%:
	cargo xtask verify --targets $(filter fvt$*-%, $(VERIFICATION_TARGETS))

lock-protocol-rcu:
	cargo xtask verify --targets lock-protocol-rcu

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