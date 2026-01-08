# Proving Facts in Distributive Systems Using Coq

This project uses Dune + Coq, managed via mise and opam.

## Prerequisites
- [mise](https://mise.jdx.dev/) - for tool version management

## First-Time Setup
```bash
# Install mise tools (opam, ocaml)
mise install

# Complete first-time setup (initialize opam, create switch, install dependencies)
mise run setup
```

## Quick Commands
```bash
mise tasks              # List all available tasks
mise run init          # Reinitialize (skips opam init)
mise run reinstall     # Reinstall dependencies only
```

## Layout
- `dune-project`: project definition
- `theories/`: Main Coq theory files
- `basics/`: Basic Coq concepts subproject
- `advanced/`: Advanced topics subproject (depends on basics)
- `.mise.toml`: task definitions

See [SUBPROJECTS.md](SUBPROJECTS.md) for details on organizing multiple subprojects.

## Available Tasks

Run `mise tasks` to see all available tasks with descriptions.

### 🔨 Build Tasks
```bash
mise run build              # Build all subprojects
mise run build-basics       # Build only basics/
mise run build-advanced     # Build only advanced/
mise run build-theories     # Build only theories/
mise run check              # Check Coq proofs
mise run watch              # Build in watch mode
mise run watch-basics       # Watch basics/ subproject
mise run clean              # Clean build artifacts
```

### 🔧 Maintenance Tasks
```bash
mise run update        # Update opam packages
mise run reinstall     # Reinstall dependencies
mise run init          # Reinitialize setup (skips opam init)
```

### 💻 Development Tasks
```bash
mise run coqtop        # Start Coq REPL
mise run format        # Format OCaml/dune files
mise run format-check  # Check formatting without changes
mise run env           # Show opam environment
```

## Example File

Check out `theories/Example.v` for a simple demonstration of Coq proofs including:
- Induction proofs
- Basic arithmetic properties
- Pattern matching and data types
- Proof tactics like `injection` and `discriminate`

## Add a Coq File
Put `.v` files under `theories/` - they will be automatically discovered by dune.

## Notes
- **OCaml/Dune files**: Formatted with ocamlformat (`.ocamlformat` config)
- **Coq files**: Use coq-lsp in your editor for formatting support
