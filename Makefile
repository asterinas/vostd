.DEFAULT_GOAL := all
.PHONY: all compile verify verify-parallel clean fmt

VERIFICATION_TARGETS := \
	lock-protocol-rcu \
	lock-protocol-rw

# Disabled:
# fvt5-lifecycle-safety
# fvt13-vmspace-unmap-safety 

COMPILE_TARGETS := vstd_extra common

# Pattern rule for individual FVT targets
fvt%:
	cargo xtask verify --targets $(filter fvt$*-%, $(VERIFICATION_TARGETS))

.PHONY: lock-protocol-rcu
lock-protocol-rcu:
	cargo xtask verify --targets lock-protocol-rcu

.PHONY: lock-protocol-rw
lock-protocol-rw:
	cargo xtask verify --targets lock-protocol-rw

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