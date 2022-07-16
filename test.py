import disconnect
import time


#print(set([(2,4),(3,4),(1,3),(2,4)]))
t1 = time.time()
fin_eds=[]
fin_st=[]
for cc in range(10):
	edges = []
	with open("./testcases_dis/edges_{}.txt".format(cc)) as f:
		for line in f:
			edges.append(tuple([int(v) for v in line.strip().split(',')]))
	s_t=[]
	with open('./testcases_dis/s_t_{}.txt'.format(cc)) as f:
		for line in f:
			s_t.append(tuple([int(v) for v in line.strip().split(',')]))
	fin_st.append(s_t)
	fin_eds.append(edges)
counter=0
for cs in range(10):
	with open('./testcases_dis/resm_{}.txt'.format(cs) , 'w') as the_file:
		for s,t in fin_st[cs]:
			the_file.write('{}\n'.format(disconnect.find_minimal(fin_eds[cs],s,t)))
			counter+=1
			print(counter)

t2 = time.time()
print(t2 - t1)
