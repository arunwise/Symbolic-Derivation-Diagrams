# script to generate ising model encodings of Px

rows = 6
cols = 6

f = open('ising.P', 'w')

# write the values and set_sw facts
f.write('values(a, [t, f]).\n')
f.write('values(bt, [t, f]).\n')
f.write('values(bf, [t, f]).\n')
f.write('set_sw(a, [0.5, 0.5]).\n')
f.write('set_sw(bt, [0.9, 0.1]).\n')
f.write('set_sw(bf, [0.9, 0.1]).\n')

f.write('\n')

# write rules for edge factor
f.write('factor(F, V1, V2) :-\n')
f.write('\t msw(a, F, V1),\n')
f.write('\t {V1=t},\n')
f.write('\t msw(bt, F, V2).\n')

f.write('\n')

f.write('factor(F, V1, V2) :-\n')
f.write('\t msw(a, F, V1),\n')
f.write('\t {V1=f},\n')
f.write('\t msw(bf, F, V2).\n')

f.write('\n')

# write the world predicate
f.write('world(')

args = ''
# horizontal edges
for r in range(1, 1+rows):
    for c in range(1, cols):
        args = args+'Fh{0}{1}V1, Fh{0}{1}V2, '.format(r,c)

# vertical edges
for c in range(1, 1+cols):
    for r in range(1, rows):
        args = args+'Fv{0}{1}V1, Fv{0}{1}V2, '.format(c,r)

# remove trailing comma and space
args = args[:-2]

f.write(args)
f.write(') :-\n')

# write msw goals
body = ''
# horizontal edges
for r in range(1, 1+rows):
    for c in range(1, cols):
        body = body+'\t factor(h{0}{1}, Fh{0}{1}V1, Fh{0}{1}V2),\n'.format(r,c)

# vertical edges
for c in range(1, 1+cols):
    for r in range(1, rows):
        body = body+'\t factor(v{0}{1}, Fv{0}{1}V1, Fv{0}{1}V2),\n'.format(c,r)

body = body[:-2]
body = body + '.\n'
f.write(body)

f.write('\n')

# write evidence predicate
f.write('evidence :-\n')
f.write('\t world({0}),\n'.format(args))

constr = ''
# write constraints
for r in range(1, 1+rows):
    for c in range(1, cols):        
        if r > 1:
            # left-up constraint
            constr = constr + '\t{{Fh{0}{1}V1 = Fv{2}{3}V2}},\n'.format(r, c, c, r-1)
            # right-up constraint
            constr = constr + '\t{{Fh{0}{1}V2 = Fv{2}{3}V2}},\n'.format(r, c, c+1, r-1)
            
        if r < rows:
            # left-down constraint
            constr = constr + '\t{{Fh{0}{1}V1 = Fv{2}{3}V1}},\n'.format(r, c, c, r)
            # right-down constraint
            constr = constr + '\t{{Fh{0}{1}V2 = Fv{2}{0}V1}},\n'.format(r, c, c+1, r)

        if c < cols-1:
            # right-right constraint
            constr = constr + '\t{{Fh{0}{1}V2 = Fh{2}{3}V1}},\n'.format(r, c, r, c+1)

# we have recorded all constraints except down down
for c in range(1, 1+cols):
    for r in range(1, rows):
        if r < rows - 1:
            # down-down constraint
            constr = constr + '\t{{Fv{0}{1}V2 = Fv{2}{3}V1}},\n'.format(c, r, c, r+1)

constr = constr[:-2]
constr = constr + '.\n'

f.write(constr)

f.write('\n')

# write query
f.write('query :- \n')
f.write('\t world({0}),\n'.format(args))

qbody = ''
# horizontal edges
for r in range(1, 1+rows):
    for c in range(1, cols):
        qbody = qbody + '\t{{Fh{0}{1}V1 = t}},\n'.format(r,c)
        qbody = qbody + '\t{{Fh{0}{1}V2 = t}},\n'.format(r,c)

# vertical edges
for c in range(1, 1+cols):
    for r in range(1, rows):
        qbody = qbody + '\t{{Fv{0}{1}V1 = t}},\n'.format(c,r)
        qbody = qbody + '\t{{Fv{0}{1}V2 = t}},\n'.format(c,r)

qbody = qbody[:-2]
qbody = qbody + '.\n'

f.write(qbody)

f.write('\n')

f.write('qe :- evidence, query.\n')
f.close()
