

with open('good_stats.txt') as f:
	lines = f.readlines()
	for line in lines:
		_a, time, size, depth, _ = map(lambda s:s.strip(), line.split('|'))
		print(size+','+time)
