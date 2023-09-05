# Coq-verified Operational transformation for tree-like data structures

[![JetBrains research project](https://jb.gg/badges/obsolete.svg)](https://confluence.jetbrains.com/display/ALL/JetBrains+on+GitHub)

This repository contains Coq source code accompanying the paper "Verified Operational 
Transformation for Trees" by S. Sinchuk, P. Chuprikov and K. Solomatov published in proceedings of 7th International Conference, ITP 2016 (pp. 358--373).
[Link to the paper](https://link.springer.com/chapter/10.1007/978-3-319-43144-4_22)

## Building
The original source code is compatible with Coq 8.4 and makes use of Ssreflect.
The repository also contains version of the code compatible with Coq 8.8 and 8.13.
Use `make -f Makefile` to build the project.
