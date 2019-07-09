

#  Raw ideas:

- Jutsification pointer is not needed for free variable occurrences!
  Pointer to the tree node suffice.
  Could simplify traversal implementation even further by introducing a new type FreeVarOccurrence<T> with no pointer.
- Alternating AST probably not needed: p-view/core could be adjusted to operate on traditional ASL
- IDEA: use memory pointers instead of array indexing to implement justification pointers.
