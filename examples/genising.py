# script to generate ising model encodings of Px
import argparse

parser = argparse.ArgumentParser()
parser.add_argument("-r", "--rows", required=True, help="number of rows")
parser.add_argument("-c", "--cols", required=True, help="number of columns")

args = vars(parser.parse_args())
rows = int(args["rows"])
cols = int(args["cols"])

f = open('ising.P', 'w')

# write type facts
f.write('type(bool, [t, f]).\n')

# write outcomes facts
f.write('outcomes(edge, [bool, bool]).\n')

# write set_sw facts
f.write('set_sw(edge, [0.49, 0.01, 0.01, 0.49]).\n')

# write down rows and cols
f.write('rows('+rows+').\n')
f.write('cols('+cols+').\n')

f.write('\n')

# 1. Compute the set of all edges.

# 2. Associate with each (row, col) a unique label that serves as # the variable name.

# 3. Also with each (row, col) associate the set of edges incident on
# that node.

edges = []
nodelabels = {}
incidentedges = {}

# horizontal edges
for i in range(rows):
    for j in range(cols-1):
        node1 = str(i)+str(j)
        node2 = str(i)+str(j+1)
        edge = 'edge_'+node1+'_'+node2
        edges.append(edge)
        if node1 not in nodelabels:
            nodelabels[node1] = 'N_'+node1+'_'+edge

        if node2 not in nodelabels:
            nodelabels[node2] = 'N_'+node2+'_'+edge

        if node1 not in incidentedges:
            incidentedges[node1] = [edge]
        else:
            incidentedges[node1].append(edge)

        if node2 not in incidentedges:
            incidentedges[node2] = [edge]
        else:
            incidentedges[node2].append(edge)

# vertical edges
for j in range(cols):
    for i in range(rows-1):
        node1 = str(i)+str(j)
        node2 = str(i+1)+str(j)
        edge = 'edge_'+node1+'_'+node2
        edges.append(edge)
        if node1 not in nodelabels:
            nodelabels[node1] = 'N_'+node1+'_'+edge

        if node2 not in nodelabels:
            nodelabels[node2] = 'N_'+node2+'_'+edge

        if node1 not in incidentedges:
            incidentedges[node1] = [edge]
        else:
            incidentedges[node1].append(edge)

        if node2 not in incidentedges:
            incidentedges[node2] = [edge]
        else:
            incidentedges[node2].append(edge)

# write the head of the evidence rule
f.write('evidence :- \n')

# write the msw part of the body
for e in edges:
    parts = e.split('_')
    f.write('\t')
    f.write('msw(edge, '+e+', [')
    f.write('N_'+parts[1]+'_'+e)
    f.write(', ')
    f.write('N_'+parts[2]+'_'+e)
    f.write(']),\n')

# write the constraints
for i in range(rows):
    for j in range(cols):
        node = str(i)+str(j)
        edgelist = incidentedges[node]
        k = 0
        while k < len(edgelist)-1:
            f.write('\t{N_'+node+'_'+edgelist[k]+' = '+'N_'+node+'_'+edgelist[k+1]+'},\n')
            k = k + 1
else:
    f.write('\ttrue.\n')

# # write the evidence rule
# f.write('\n')
# f.write('evidence :- world(')
# f.write(', '.join(list(nodelabels.values())))
# f.write(').\n')

# write the query rule
f.write('\n')
f.write('query :- \n')
# f.write('\tworld(')
# f.write(', '.join(list(nodelabels.values())))
# f.write('),\n')
# for node in list(nodelabels.values()):
#     f.write('\t{'+node+' = t},\n')
# else:
#     f.write('\ttrue.\n')
for e in edges:
    parts = e.split('_')
    f.write('\t')
    f.write('msw(edge, '+e+', [')
    f.write('N_'+parts[1]+'_'+e)
    f.write(', ')
    f.write('N_'+parts[2]+'_'+e)
    f.write(']),\n')
    f.write('\t{N_'+parts[1]+'_'+e+' = t},')
    f.write('\t{N_'+parts[2]+'_'+e+' = t},\n')

f.write('\ttrue.\n')
f.write('\n')

# write conjunction of query and evidence
f.write('qe :- evidence, query.\n')

f.close()
