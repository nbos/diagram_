# Default target is debug
.PHONY: default
default: debug

# Debug build with no optimization
.PHONY: debug
debug:
	@echo "Building debug version..."
	cabal build --ghc-options="-O0"
	@echo "Debug build complete."

# Release build with full optimization and additional options
.PHONY: release
release:
	@echo "Building release version..."
	cabal build --ghc-options="-Wall -O2 -threaded -rtsopts -with-rtsopts=-N"
	@echo "Release build complete."

# Clean build artifacts
.PHONY: clean
clean:
	@echo "Cleaning build artifacts..."
	cabal clean
	@echo "Clean complete."

# Run the program
.PHONY: run
run: debug
	@echo "Running program (debug version)..."
	cabal run diagram
