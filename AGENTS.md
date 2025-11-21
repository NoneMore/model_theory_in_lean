# AGENTS.md

This file provides guidance to agents when working with code in this repository.

## Build/Lint/Test Commands

- `lake build`: Build the project.
- `lake lint`: Lint the project. Note that the project follows the `mathlib` standard linter ruleset.
- `lake test`: Run tests. Currently, there are no tests in the project.

## Code Style and Conventions

The project follows the `mathlib` coding standards. Key non-obvious guidelines are summarized below. For full details, see the `.doc/` directory.

### Naming
- **Files:** `UpperCamelCase` (e.g., `MyFile.lean`).
- **Types/Props:** `UpperCamelCase` (e.g., `IsMonoid`).
- **Theorems/Proofs:** `snake_case` (e.g., `mul_one`).
- **Functions/Terms:** `lowerCamelCase` (e.g., `toFun`).
- **Spelling:** Use American English for all declaration names.

### Documentation
- **File Header:** All files must start with a copyright header, author list, and a module docstring (`/-! ... -/`).
- **Docstrings:** All public definitions and major theorems require a docstring (`/-- ... -/`).
- **Language:** All documentation must be in English.

### Formatting
- **Line Length:** Keep lines under 100 characters.
- **Indentation:** 2 spaces for proofs and definition bodies.
- **Anonymous Functions:** Use `fun x ↦ ...`.
- **Application:** Prefer `<|` over `$`.

## Architecture

- The project is a Lean 4 library for model theory.
- The main entry point is `ModelTheoryInLean.lean`.
- Core concepts are defined in the following files:
    - `ModelTheoryInLean/Definability.lean`: Defines definability.
    - `ModelTheoryInLean/Ominimal/Basic.lean`: Defines o-minimal structures.
    - `ModelTheoryInLean/Ominimal/Semialgebriac/Basic.lean`: Defines semialgebraic sets.

## Development Process

- The project is developed in a TODO-driven manner. Check the `TODO` comments in the source files for future development directions.
- Unfinished proofs are marked with `sorry`.

## Tooling

### MCP Server: `lean-lsp`

This server provides essential tools for interactive Lean development. Use these tools iteratively to write and debug proofs. The most critical tools are enabled by default (`alwaysAllow`).

**Core Tools & Usage:**

-   **`lean_goal`**: **Your most important tool.** Use it inside a tactic block (e.g., right before a `sorry`) to see the current proof state, including hypotheses and goals.
-   **`lean_diagnostic_messages`**: Check for errors, warnings, and information messages in a file. Essential for debugging broken proofs.
-   **`lean_hover_info`**: Get the type and documentation for any identifier (variable, function, theorem) by providing its location.
-   **`lean_local_search`**: Quickly search for declarations (theorems, definitions) within the current project and its dependencies (like `mathlib`). This is very fast and should be your first choice for finding lemmas.
-   **`lean_leansearch` & `lean_loogle`**: If `lean_local_search` doesn't find what you need, use these to search the public `mathlib` library.
    -   `lean_leansearch`: Best for natural language queries (e.g., "addition is commutative").
    -   `lean_loogle`: Best for queries based on Lean syntax, types, or subexpressions (e.g., `?a + ?b = ?b + ?a` or `|- _ < _ → _`).
-   **`lean_declaration_file`**: Jump to the source file where a symbol is defined.

**Example Proof-Writing Workflow:**

1.  **State the Theorem and Start the Proof**: Write your theorem statement and begin the proof with `by sorry`.
2.  **Inspect the Goal**: Use `lean_goal` at the position of `sorry` to understand what needs to be proven.
3.  **Find Relevant Lemmas**:
    *   Start with `lean_local_search` using keywords related to your goal.
    *   If that fails, try `lean_leansearch` with a natural language description of what you want to prove.
    *   Alternatively, use `lean_loogle` with a pattern that matches your goal's structure.
4.  **Understand the Lemma**: Once you find a promising lemma (e.g., `add_comm`), use `lean_hover_info` on its name to see its exact statement and documentation.
5.  **Apply the Lemma**: Replace `sorry` with a tactic using the lemma, for example, `rw [add_comm]`.
6.  **Check Progress**: Use `lean_goal` again to see the new proof state.
7.  **Debug Errors**: If you introduce an error, use `lean_diagnostic_messages` to understand the problem. Use `lean_hover_info` on terms to check their types.
8.  **Repeat**: Continue this iterative process of inspecting the goal, finding lemmas, and applying tactics until the message "no goals to be solved" appears.