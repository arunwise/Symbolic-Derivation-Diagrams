# 1. To transform PLP programs
* Load xform.pl (in XSB this is ?- [xform].)
* Run: ?- transform_file('inputfile', 'outputfile')
# 2. To generate OSDD for query q(v1,...,vn) 
* Load bounds, syminfer.pl, and transformed file 'outputfile' (in XSB this is ?- [bounds, syminfer, 'outputfile'].)
* Run: ?- q(v1,....,vn,leaf(1),O) 
  where O contains the required OSDD
# 3. To visualize OSDDs
* In the XSB interpreter:  set_prolog_flag(write_attributes, ignore)
* Generate OSDD O and use writeDot(O, 'dotfile.dot')
* Install and use 'dot' tool to generate PNG/PDF or other format file
  $ dot -Tpdf dotfile.dot -o dotfile.pdf
