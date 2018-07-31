# Transforming PLP programs to support symbolic inference
* Load xform.pl (in XSB this is `?- [xform].`)
* Run: `?- transform_file('inputfile', 'outputfile')`
* The `type/2` facts should precede `outcome/2` facts which inturn preced `set_sw/2` facts in the `inputfile`.
# Generating an OSDD for query q(v1,...,vn) 
* Load syminfer.pl, and transformed file 'outputfile' (in XSB this is `?- [syminfer, 'outputfile'].`)
* Run: `?- compute_osdd(q(v1,....,vn), O).`
* It is assumed that `q(v2,...,vn)` is a ground query and `v1,...,vn`
  are constants from the `values/2` declarations.
* `O` will unify with the computed OSDD
# Compute probability of an OSDD
* Compute OSDD `O` as described above.
* If `O` doesn't satisfy conditions for measurability use `?- probability(O, P).`
* If `O` satisfies conditions for measurability use `?- probability_m(O, P).`
# Visualizing OSDDs
* Generate OSDD `O` and use: `?- writeDot(O, 'dotfile.dot').`
* Install and use `dot` tool to generate PNG/PDF or other format file
* Use: `$ dot -Tpdf dotfile.dot -o dotfile.pdf` to transform to PDF
# Notes
* Implementation of OSDD exact inference algorithms described in [Constraint-Based Inference in Probabilistic Logic Programs](https://easychair.org/publications/preprint_download/pmTQ)
