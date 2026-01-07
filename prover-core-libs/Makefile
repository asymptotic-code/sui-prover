.PHONY: setup clean help

# Sui framework repository
SUI_REPO = https://github.com/asymptotic-code/sui.git
SUI_DIR = sui
SUI_FRAMEWORK_PATH = $(SUI_DIR)/crates/sui-framework/packages

# Local prover packages (relative to prover-core-libs directory)
PROVER_PACKAGES = ../../packages

# Symlinks directory
SYMLINKS_DIR = packages

help:
	@echo "Makefile for setting up prover-core-libs"
	@echo ""
	@echo "Targets:"
	@echo "  setup  - Clone sui framework and create all symlinks"
	@echo "  clean  - Remove all symlinks and cloned repository"
	@echo "  help   - Show this help message"

setup: clone-sui create-symlinks
	@echo ""
	@echo "=========================================="
	@echo "Setup complete!"
	@echo "=========================================="
	@echo ""
	@echo "To use the local framework packages, run:"
	@echo ""
	@echo "  cd specs/move-stdlib"
	@echo "  SUI_PROVER_FRAMEWORK_PATH=$(PWD)/packages sui-prover --timeout 60 --force-timeout --skip-spec-no-abort"
	@echo ""

clone-sui:
	@echo "Cloning sui repository (shallow clone)..."
	@if [ ! -d "$(SUI_DIR)" ]; then \
		git clone --depth 1 --filter=blob:none --sparse $(SUI_REPO) $(SUI_DIR); \
		cd $(SUI_DIR) && git sparse-checkout set crates/sui-framework/packages; \
		echo "Cloned sui to $(SUI_DIR)"; \
	else \
		echo "sui repository already exists at $(SUI_DIR)"; \
	fi

create-symlinks:
	@echo "Creating symlinks in $(SYMLINKS_DIR)..."
	@rm -rf packages
	@mkdir -p packages
	@# Framework packages from cloned sui repo (relative paths)
	@ln -s ../$(SUI_FRAMEWORK_PATH)/bridge $(SYMLINKS_DIR)/bridge
	@ln -s ../$(SUI_FRAMEWORK_PATH)/deepbook $(SYMLINKS_DIR)/deepbook
	@ln -s ../$(SUI_FRAMEWORK_PATH)/move-stdlib $(SYMLINKS_DIR)/move-stdlib
	@ln -s ../$(SUI_FRAMEWORK_PATH)/sui-framework $(SYMLINKS_DIR)/sui-framework
	@ln -s ../$(SUI_FRAMEWORK_PATH)/sui-system $(SYMLINKS_DIR)/sui-system
	@# Prover packages from local sui-prover-2026 (relative paths)
	@ln -s $(PROVER_PACKAGES)/prover $(SYMLINKS_DIR)/prover
	@ln -s $(PROVER_PACKAGES)/sui-prover $(SYMLINKS_DIR)/sui-prover
	@ln -s $(PROVER_PACKAGES)/sui-specs $(SYMLINKS_DIR)/sui-specs
	@echo ""
	@echo "Created symlinks:"
	@ls -la $(SYMLINKS_DIR) | grep "^l"

clean:
	@echo "Cleaning up..."
	@rm -f $(SYMLINKS_DIR)/bridge $(SYMLINKS_DIR)/deepbook $(SYMLINKS_DIR)/move-stdlib \
	       $(SYMLINKS_DIR)/sui-framework $(SYMLINKS_DIR)/sui-system \
	       $(SYMLINKS_DIR)/prover $(SYMLINKS_DIR)/sui-prover $(SYMLINKS_DIR)/sui-specs
	@if [ -d "$(SUI_DIR)" ]; then \
		echo "Removing cloned sui repository..."; \
		rm -rf $(SUI_DIR); \
	fi
	@echo "Clean complete!"
