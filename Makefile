# Default target is fast build
.PHONY: default
default: fast

# Fast build with no optimization and no profiling
.PHONY: fast
fast:
	@echo "Building fast version (no profiling, -O0)..."
	cabal build --ghc-options="-O0"
	@echo "Fast build complete."

# Debug build with profiling for stack traces
.PHONY: debug
debug:
	@echo "Building debug version with profiling..."
	cabal build --enable-profiling --ghc-options="-O0 -fprof-auto -fprof-cafs -rtsopts"
	@echo "Debug build complete."

# Release build with full optimization
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

# # Run with profiling and stack traces
# .PHONY: run-debug
# run-debug: debug
# 	@echo "Running program with profiling and stack traces..."
# 	cabal run diagram -- +RTS -xc -RTS
