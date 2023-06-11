RISCV_PREFIX = riscv64-elf-
# RV32UI = $(wildcard riscv-tests/isa/rv32ui/*.S)
TESTS = riscv-tests/isa
RV32UI = $(patsubst $(TESTS)/rv32ui/%.S,%,$(wildcard $(TESTS)/rv32ui/*.S))

.PHONI = riscv-tests-rv32ui
riscv-tests-rv32ui:
	git submodule update --init --recursive
	RISCV_PREFIX=$(RISCV_PREFIX) make -C riscv-tests/isa rv32ui
	$(foreach var,$(RV32UI),$(RISCV_PREFIX)objcopy -O binary $(TESTS)/rv32ui-p-$(var) $(TESTS)/rv32ui-p-$(var).bin;)

# $(RISCV_PREFIX)-objcopy -O binary rv32ui-p-add rv32ui-p-add.bin

