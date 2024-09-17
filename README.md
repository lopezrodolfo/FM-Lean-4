# Natural Numbers Implementation and Proofs in Lean

This Lean project contains implementations and proofs of various properties of natural numbers, including:

- Definition of natural numbers (mynat)
- Basic arithmetic operations (addition, multiplication)
- Proofs of fundamental properties (associativity, commutativity, distributivity)

## Author

Rodolfo Lopez

## Date

Fall 2022

## Installation

To run this project, you need to install Lean. The recommended way is to use elan, the Lean version manager:

1. Install elan:

   - On Unix-like systems (Linux, macOS):
     ```
     curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
     ```
   - On Windows:
     ```
     curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1 -sSf | powershell -c -
     ```

2. Restart your terminal or run `source ~/.profile` (or equivalent for your shell).

3. Install Lean:

   ```
   elan install leanprover/lean:stable
   ```

4. Verify the installation:
   ```
   lean --version
   ```

For more detailed instructions, visit the [Lean website](https://leanprover.github.io/lean4/doc/setup.html).

## Usage

Open the `hw4.lean` file in a Lean-compatible editor to view and evaluate the code.

## File Structure

- `hw4.lean`: Contains the implementation of mynat and proofs of its properties

## Key Concepts

The project covers the following Lean concepts:

- Inductive type definitions
- Recursive function definitions
- Theorem proving using tactics
- Induction proofs

## Key Definitions and Theorems

- `mynat`: Custom implementation of natural numbers
- `add`: Addition operation for mynat
- `mul`: Multiplication operation for mynat
- `zero_add`: Proof that 0 + n = n for any n
- `add_assoc`: Proof of associativity of addition
- `add_comm`: Proof of commutativity of addition
- `mul_add`: Proof of left distributivity of multiplication over addition
- `mul_assoc`: Proof of associativity of multiplication
- `mul_comm`: Proof of commutativity of multiplication

To interact with the proofs, use a Lean-compatible editor that supports tactic state visualization.
