import sys,pprint,pdb,traceback

def DPLL(clauses,symbols,model):
	''' Implements DPLL algorithm
	Parameter: 
	Input: 
	a. clauses: list of clauses from CNF
	b. symbols: list of symbols from CNF
	c. model: values of symbols
	Output:
	returns result with true or false for satisfiablity and model '''
	
	
	
	#if every clause in clauses is true in model then return true
	clauses_length=len(clauses)	
	if clauses_length == 0:
		result={"isSAT":1,"model":model}
		return result
	
		
	#if some clause in clauses is false in model then return false
	for i in range(clauses_length):
		if len(clauses[i])==0:
			result={"isSAT":0,"model":model}
			return result
	
	
	
	# P, value = FIND-PURE-SYMBOLS(symbols, clauses, model)
	# update all 3 after this call
	Pvalue=findPureSymbols(symbols, clauses, model)
	
	if len(Pvalue["identifiedSyms"])>0:
		updatedDS = updateDS(Pvalue,symbols, clauses, model)
		symbols=updatedDS["symbols"]
		clauses=updatedDS["clauses"]
		model=updatedDS["model"]
	
		return DPLL(clauses,symbols,model)
	
	
	#P, value  FIND-UNIT-CLAUSE(clauses, model)
	# update all 3 after this call
	Pvalue=findUnitClause(clauses, model)
	if len(Pvalue["identifiedSyms"])>0:
		updatedDS = updateDS(Pvalue,symbols, clauses, model)
		symbols=updatedDS["symbols"]
		clauses=updatedDS["clauses"]
		model=updatedDS["model"]
	
		return DPLL(clauses,symbols,model)
	
	
	
	
	
	# P <- FIRST(symbols); rest <- REST(symbols)	
	
	# update clauses, so that model and symbols will be handled in the recursive call below
	cclauses=eval(str(clauses))
	
	clause=0
	if isinstance(clauses[clause],list):
		if len(clauses[clause]) >1 and 	clauses[clause][0] =="not":
			clauses.append(clauses[clause])
			cclauses.append(complement_symbol(clauses[clause]))
			
		elif len(clauses[clause]) >1:
			clauses.append(clauses[clause][1])
			cclauses.append(complement_symbol(clauses[clause][1]))
			
		elif len(clauses[clause]) ==1:
			clauses.append(clauses[clause])
			cclauses.append(complement_symbol(clauses[clause]))
			
	else:
		if clauses[clause]=="or":
			clauses.append(clauses[clause+1])
			cclauses.append(complement_symbol(clauses[clause+1]))
			
		else:
			clauses.append(clauses[clause])
			cclauses.append(complement_symbol(clauses[clause]))
			
	
	cmodel=eval(str(model))
	cl=DPLL(clauses,symbols,model)
	
	if cl["isSAT"] == 1:
		return cl
		
	clc=DPLL(cclauses,symbols,model)
	
	if (cl["isSAT"] or clc["isSAT"]) == 0:
		return {"isSAT":0,"model":{}}

	
	elif clc["isSAT"] == 1:
		return clc

def findUnitClause(clauses, model):
	''' Find unit clauses from given clause list. Deletes clause or its complement literal'''
	
	unitSyms=[]
	
	# [[[not q]]], [not p], [ [not p],q], [[q]]
	# Iterate through clauses to find unit symbols
	for i in range(len(clauses)):
		if isinstance(clauses[i],list):
			if len(clauses[i]) <3 and len(clauses[i])>0:
				if clauses[i][0]=="not":
					if clauses[i] not in unitSyms:
						unitSyms.append(clauses[i])
				elif isinstance(clauses[i][0],list):
					if clauses[i][0] not in unitSyms:
						unitSyms.append(clauses[i][0])
				elif len(clauses[i][0]) == 1:
					unitSyms.append(clauses[i][0])
		else:
			if clauses[i] not in unitSyms:
				unitSyms.append(clauses[i])



					
	for units in unitSyms:
		clause=0
		while clause < len(clauses):
		# for [[]]
			if isinstance(clauses[clause],list) and len(clauses[clause])>0:
				if clauses[clause][0]!="not":
					syms=0
					while syms < len(clauses[clause]):
					# for [[[]]]
						
						if isinstance(clauses[clause][syms],list):
							if clauses[clause][syms][0] !="not":
								if clauses[clause][syms][0] == units:
									del clauses[clause]
									clause-=1
									break
								if complement_symbol(clauses[clause][syms][0]) == units:
									del clauses[clause][syms][0]
									syms-=1
						
						else:
							if clauses[clause][syms] == units:
								del clauses[clause]
								clause-=1
								break
							if complement_symbol(clauses[clause][syms]) == units:
								del clauses[clause][syms]
								syms-=1
						syms+=1
				else:
					if clauses[clause] == units:
					 	del clauses[clause]
					 	continue
					elif complement_symbol(clauses[clause])== units:
					 	clauses[clause]=[]
					 	clause+=1
					 	continue
			elif isinstance(clauses[clause],list) and len(clauses[clause])>0 and len(clauses[clause]) <3:
				if clauses[clause][0] == "or":
					del clauses[clause][0]	
			elif clauses[clause]== units:
				del clauses[clause]
				clause-=1
			clause+=1
	
	
	# remove redundant ORS
	clause=0
	while clause < len(clauses):
		if isinstance(clauses[clause],list) and len(clauses[clause])>0 and len(clauses[clause]) <3:
			if clauses[clause][0] == "or":
				del clauses[clause][0]	
		clause +=1
	
	return 	{"identifiedSyms":unitSyms,"clauses":clauses}

def complement_symbol(sym):
	''' Generates complement of a symbol '''
	if isinstance(sym,list):
		if sym[0]=="not":
			return sym[1]
	else:
		return ["not",sym]

def findPureSymbols(symbols, clauses, model):
	''' Generates list of pure symbols from clauses '''

	operationsList=["or","and","iff","implies","not"]
	syms=generateSymbolList(clauses)
	length=0
	pureSyms=[]
	# get pure symbols from all symbols
	while length < len(syms):
		if isinstance(syms[length], list):
			if syms[length][1] not in syms:
				pureSyms.append(syms[length])
		else:
			if ["not",syms[length]] not in syms:
				pureSyms.append(syms[length])
		length +=1
	
	# iterate through all clauses to see if they are in pure symbols; remove them from clauses
	clause=0
	if isinstance(clauses,list):
		if clauses[0] != "not":
		# for [[]]
			while clause < len( clauses):
				if isinstance(clauses[clause],list):
					if clauses[clause][0] != "not":
						sym=0
						while sym < len(clauses[clause]):
							# for [[[]]]
							if isinstance(clauses[clause][sym],list) and clauses[clause][sym][0] != "not":
								if clauses[clause][sym][0] in pureSyms:
									del clauses[clause]
									clause-=1
									break
							elif clauses[clause][sym] in pureSyms:
								del clauses[clause]
								clause-=1
								break
							sym+=1
					else:
						if clauses[clause] in pureSyms:
							clauses=[]
							break
				else:
					if clauses[clause] in pureSyms:
						clauses=[]
						break
				clause+=1
		else:
			if clauses in pureSyms:
				clauses=[]				
		
	return 	{"identifiedSyms":pureSyms,"clauses":clauses}		
		

def updateDS(Pvalue,symbols, clauses, model):
	''' clauses = reduced clauses, symbols - P, model UNION {P=value} '''
	
	clauses=Pvalue["clauses"]
	symbols[:]= [ sym for sym in symbols if sym not in Pvalue["identifiedSyms"]  ]
	for sym in Pvalue["identifiedSyms"]:
		if isinstance(sym, list):
			if sym[1] not in model:
				if complement_symbol(sym) not in Pvalue["identifiedSyms"]:
					model.update({sym[1]:0})
		elif sym not in model:
			if complement_symbol(sym) not in Pvalue["identifiedSyms"]:
				model.update({sym:1})
	
	return {"symbols":symbols,"model":model,"clauses":clauses}
	
	
	

def formInput(CNF):
	''' Generates the clauses, symbols and model for DPLL
	Input: CNF -> CNF statement
	Output: Dictionary of above elements
	result={"clauses":clauses,"symbols":symbols,"model":model} '''
	
	
	clauses=generateClauses(CNF)
	symbols=generateSymbolList(clauses)
	
	#model= dict(zip([str(i) for i in  symbols],[0]*len(symbols)))
	model={}
	result={"clauses":clauses,"symbols":symbols,"model":model}
	
	return result


def generateClauses(CNF):
	''' Generates clauses from CNF statement'''
	clauses=CNF
	if len(CNF)>1:
		if CNF[0]=="and":
			clauses=CNF[1:]
	return clauses
		
		
def generateSymbolList(clauses):
	''' Generates symbols for clauses - [Note: this is NOT a pure symbol list i.e., P and !P both are included]
	Input: CNF statement
	Output: Symbol list  '''
	
	operationsList=["or","and","iff","implies","not"]
	symbols=[]
	length=0
	if isinstance(clauses, list):
		if len(clauses)>1 and clauses[0] == "not" and (not isinstance(clauses[1], list)):
					if clauses not in symbols:
						symbols.append(clauses)
		else:
			while length<len(clauses):
				if isinstance(clauses[length], list):
			
					# recursive call through all grandchilds
				
					# special case for NOT
					if len(clauses[length])>1 and clauses[length][0] == "not" and (not isinstance(clauses[length][1], list)):
						if clauses[length] not in symbols:
							symbols.append(clauses[length])
				 	else:
					 	childSymbols=generateSymbolList(clauses[length])
					 	clen=0
					 	while clen<len(childSymbols):
					 		if childSymbols[clen] not in operationsList and childSymbols[clen] not in symbols:
					 			symbols.append(childSymbols[clen])
					 		clen+=1
				else:
					if clauses[length] not in operationsList and clauses[length] not in symbols:
						symbols.append(clauses[length])
				length+=1
	else:
		if clauses not in operationsList:
			symbols.append(clauses)
	return symbols

	
def getSatisfiability(arg):
	''' Reads input file containing CNF statements and returns Satisfiabiltiy of them in a file called CNF_satisfiability.txt
	Parameters: 
	Input:
	a. arg - Array containing options to run the script with. Third element must be the input file name
	Output: None '''
	
        args = len(arg)
        if args<3:
                print("Provide input file after script name.\nUsage: python DPLL.py -i inputfilename ")
        else:
                try:
                	inputFileName=arg[2]
                	
                	# Read input file
                	with open(inputFileName,"r") as inputFile:
                		totLines=int(inputFile.readline())
                		print(totLines)
                		iterator=0
                		#pdb.set_trace()
                		# Create context for output file
                		with open("CNF_satisfiability.txt","w") as oFile:
		        		# Loop through the input file to read PL sentences (PL: Propositional Logic)
		        		while iterator < totLines:
		        			global done
						done=0
		        			currCNF = eval(inputFile.readline())
		        			try:
							# Fucntion call to evaluate CNF
							result=formInput(currCNF)
							satResult=DPLL(result["clauses"],result["symbols"],result["model"])
							
							outString=[]
							# {'isSAT': 1, 'model': {'B': 1, 'R': 1}}
							if satResult["isSAT"] == 1:
							
								# clean model: since some symbols can have any values, model wont have any value for them
								if len(result["symbols"]) > 0:
									for sym in result["symbols"]:
										if isinstance(sym, list):
											if sym[1] not in satResult["model"]:
													satResult["model"].update({sym[1]:0})
										elif sym not in satResult["model"]:
												satResult["model"].update({sym:1})	
							
								outString.append("true")
							
								for items in satResult["model"]:
									varaibleModel=""
									varaibleModel+=str(items)
								
									if satResult["model"][items] ==1 :
										varaibleModel+="=true"
									else:
										varaibleModel+="=false"	
									outString.append(varaibleModel)
							
							else:
								outString.append("false")
							
							print(outString)
							oFile.write(str(outString))
							oFile.write("\n")
						except Exception as excq:
							traceback.print_exc()
							print(excq.args)
		        			iterator+=1
                
                except Exception as exc:
                	traceback.print_exc()
                        print(exc.args)
                        

                                
        
if __name__ == "__main__":
   getSatisfiability(sys.argv)
