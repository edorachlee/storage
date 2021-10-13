# Dynamic Storage Operations
 A C implementation of dynamic storage operations.

Author: Chang Hi Lee(lee.c@wustl.edu)

Title: Dynamic Memory Allocator

Function: This is a C implementation of the dynamic storage operations malloc, free, and realloc, with heap consistency checking and free memory block coalescing for allocation efficiency.

Usage: Usage functionalities have been removed(see note below). Code is provided mainly as read-only purposes.

Main Files:
- mm.{c,h}: C implementations of malloc, free, and realloc with supporting functions
- memlib.{c,h}: Models the heap and sbrk functions

Development: I implemented my own versions of the memory allocation routines malloc, free, and realloc, along with supporting functions for these routines. Notably, I included a heap checker to verify heap consistency as I dynamically initialized and deleted pointers to memory blocks, and also a coalesce function to efficiently access free memory blocks. Debugging was performed with the gdb tool in combination with breakpoints and assert statements.

Note: Performed as part of school work. Course number and instructor information have been omitted to prevent plagiarism. My personal work is represented by "mm.c". Any other file does not represent my work.
