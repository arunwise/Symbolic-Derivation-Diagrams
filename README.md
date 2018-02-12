# Transforming PLP programs to OSDD programs
* Load xform.pl (in XSB this is `?- [xform].`)
* Run: `?- transform_file('inputfile', 'outputfile')`
* It is assumed that all `values/2` declarations appear before any other lines of code in 'inputfile'.
# Generating an OSDD for query q(v1,...,vn) 
* Load bounds, syminfer.pl, and transformed file 'outputfile' (in XSB this is `?- [bounds, syminfer, 'outputfile'].`)
* Run: `?- q(v1,....,vn,leaf(1),O).`
* O will unify with the computed OSDD
# Visualizing OSDDs
* In the XSB interpreter: `?- set_prolog_flag(write_attributes, ignore)`
* Generate OSDD O and use: `?- writeDot(O, 'dotfile.dot').`
* Install and use `dot` tool to generate PNG/PDF or other format file
* Use: `$ dot -Tpdf dotfile.dot -o dotfile.pdf` to transform to PDF
