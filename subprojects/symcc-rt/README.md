# SymCC Runtime

SymCC Runtime exposes a standard set of functions usable in different Symbolic
Execution-related projects as a backend linkable statically and dynamically.

## Build

To compile `symcc-rt`, run:

```bash
$ git submodule update --init --recursive
$ mkdir build && cd build
$ cmake ..
$ ninja
```

It will compile both `libsymcc-rt.so` (shared library) and `libsymcc-rt.a`
(static library) in the `build` directory.

## Relation with SymCC

SymCC Runtime was originally a subdirectory of
[SymCC](https://github.com/eurecom-s3/symcc) under the `runtime` directory. It
has been moved out be more easily usable as a library in different projects,
which are not necessarily related to SymCC's compiler pass.

The export of SymCC Runtime was done at the commit pointed by
`3f98002a66f18a5c09856c5e66a6c1e48b0ee1a9`.  The tag `export_runtime_from_symcc`
points to the last commit for which `symcc-rt` was the `runtime` subdirectory of
`symcc`.  It has some implications:
- **Pull request IDs** and **Issue IDs** before this commit refer to
  [SymCC](https://github.com/eurecom-s3/symcc) IDs.
- `symcc-rt` is imported as a submodule in SymCC.

## Citation

If you wish to use this in your scientific work, please cite the SymCC paper:
``` bibtex
@inproceedings {poeplau2020symcc,
  author =       {Sebastian Poeplau and Aurélien Francillon},
  title =        {Symbolic execution with {SymCC}: Don't interpret, compile!},
  booktitle =    {29th {USENIX} Security Symposium ({USENIX} Security 20)},
  isbn =         {978-1-939133-17-5},
  pages =        {181--198},
  year =         2020,
  url =          {https://www.usenix.org/conference/usenixsecurity20/presentation/poeplau},
  publisher =    {{USENIX} Association},
  month =        aug,
}
```

More information on the paper is available
[here](http://www.s3.eurecom.fr/tools/symbolic_execution/symcc.html).

## Contributing

We welcome Issues and Pull requests. If you wish to contribute, please have a
look to the `CONTRIBUTING.md` file.

## Bug reporting

We appreciate bugs with test cases and steps to reproduce, PR with
corresponding test cases. SymCC Runtime is currently understaffed, we hope to
catch up and get back to active development at some point.

## Contact

Feel free to use GitHub issues and pull requests for improvements, bug reports,
etc. Alternatively, you can send an email to Sebastian Poeplau
(sebastian.poeplau@eurecom.fr) and Aurélien Francillon
(aurelien.francillon@eurecom.fr).

## License

SymCC Runtime is free software: you can redistribute it and/or modify it under
the terms of the GNU Lesser General Public License as published by the Free
Software Foundation, either version 3 of the License, or (at your option) any
later version.  See [SymCC#114](https://github.com/eurecom-s3/symcc/issues/114)
for the rationale.

SymCC Runtime is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE. See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU
Lesser General Public License along with SymCC Runtime. If not, see
<https://www.gnu.org/licenses/>.

The following pieces of software have additional or alternate copyrights,
licenses, and/or restrictions:

| Program       | Directory           |
|---------------|---------------------|
| QSYM          | `backend/qsym/qsym` |
