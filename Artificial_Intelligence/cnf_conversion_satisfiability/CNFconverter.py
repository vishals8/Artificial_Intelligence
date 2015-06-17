import sys,pprint,pdb,traceback

done=0
# Used to halt OR operation before negation

def getCNF(PL):
	''' Contains logic to convert propositional logic statment to CNF
	Parameters:
	Input:
	a. PL - List contaning a sentence in propositional logic
	Output: String containing CNF sentence '''
	
	
	# <=> ,  => , ! elimination
	PL=resolveChild(PL)
	
	if isinstance(PL, list):
		length=len(PL)-1
		while length >0:
			if isinstance(PL[length], list):
				if len(PL[length])>0:
					PL[length]=resolveChild(PL[length])
			length-=1
	global done
	done=1
	
	# distributivity of OR
	PL=resolveChild(PL)
	
	if isinstance(PL, list):
		length=len(PL)-1
		while length >0:
			if isinstance(PL[length], list):
				if len(PL[length])>0:
					PL[length]=resolveChild(PL[length])
			length-=1
	else:
		PL=list(PL)
	
	# Combine all ORs
	PL=combineORs(PL)
	
	return PL	


def combineORs(PL):
	''' Contains recursive logic to combine OR statements 
	Parameters:
	Input:
	a. PL - List contaning a sentence in propositional logic
	Output: Combined children if OR statement '''
	
	
	if isinstance(PL, list):
		if PL[0]=="or":
			temp=[]
			temp.append(PL[0])
			length=len(PL)-1
			while length >0:
				if isinstance(PL[length], list):
					if len(PL[length])>0:
						# IF parent and child both have ORs; recur to check if grandchildren have the same structure
						if PL[length][0]=="or":
							PL[length]=combineORs(PL[length])
				if isinstance(PL[length], list):
					if len(PL[length])>0:
						# IF parent and child both have ORs, combine them
						if PL[length][0]=="or":
							
							cLen=len(PL[length])-1
							while cLen>0:
								temp.append(PL[length][cLen])
								cLen-=1
								
						else:	
							temp.append(PL[length])
				else:	
					temp.append(PL[length])
				
				length -=1
			PL=[]
			cLen=0
			while cLen<=len(temp)-1:
				PL.append(temp[cLen])
				cLen+=1
		else:
			length=len(PL)-1
			# IF only child has OR, recur to check if children have OR
			while length >0:
				if isinstance(PL[length], list):
						if len(PL[length])>0:
							
							PL[length]=combineORs(PL[length])
				length -=1								
	temp=[]
	for el in PL:
		if el not in temp:
			temp.append(el)
	PL=temp	
	if len(PL)<3:
		if PL[0]=="or":
			PL=PL[1]
	
	return PL
def resolveChild(PL):
	''' Calls appropriate function 
	Parameters:
	Input:
	a. PL - Propositional logic statement
	Output: PL after function operation '''
	global done
	if PL[0]=="implies":
		PL=eliminateIF(PL)
	elif PL[0]=="or" and done==1:
		PL=pushDisjunction(PL)
	elif PL[0]=="not":
		PL=eliminateDNEG(PL)
	elif PL[0]=="iff":
		PL=eliminateIFF(PL)
	elif PL[0]=="and":
		PL=eliminateAND(PL)
	#print(PL)
	return PL
		

def eliminateAND(PL):
	''' Associativity of AND
	Parameters:
	Input:
	a. PL - List supposedly containing AND operation as first element
	Output: List with extra AND removed '''
	
	if len(PL)<1:
		print ("Empty list to eliminateAND. ")
		return PL
		
	if PL[0]!="and":
		return PL
		
	# Solve for childrens first
	if isinstance(PL, list):
		length=len(PL)-1
		while length >0:
			if isinstance(PL[length], list):
				if len(PL[length])>0:
					PL[length]=resolveChild(PL[length])
			length-=1
		
	# Associativity -> (P & Q) & (R & S) ; (P & Q) & (R) ; (P & Q) & (S). Also A & (B & (C & D) ) = &, A,B,C,D
	if isinstance(PL, list):
		if PL[0]=="and":
			length=1
			temp=[]
			temp.append(PL[0])
			while length < len(PL):
			
				if isinstance(PL[length], list):
					if PL[length][0]=="and":
						temp.append(PL[0])
						ilength=len(PL[length])-1
						while ilength>0:
							temp.append(PL[length][ilength])
							ilength-=1
					else:
						temp.append(PL[length])	
				else:
					temp.append(PL[length])
				length+=1
					
			PL=[]
			length=0
			while length<len(temp):
				PL.append(temp[length])
				length+=1
				
			
	
	temp=[]
	# Remove dupilcate elements P & P & P
	for el in PL:
		if el not in temp:
			temp.append(el)
	
	PL=temp						
	if len(PL)<3:
			if PL[0]=="and":
				PL=PL[1]
	return PL 

def eliminateIFF(PL):
	''' Removes  Double implication
	Parameters:
	Input:
	a. PL - List supposedly containing Bi-conditional operation as first element
	Output: List with IFF converted '''
	
	if len(PL)<1:
		print ("Empty list to eliminateIFF. ")
		return PL
	if PL[0]=="iff":
		# Solve for childrens first
		if isinstance(PL, list):
			length=len(PL)-1
			while length >0:
				if isinstance(PL[length], list):
					if len(PL[length])>0:
						PL[length]=resolveChild(PL[length])
				length-=1 
		temp=[]
		temp.append("and")
		temp.append(["implies",PL[1],PL[2]])
		temp.append(["implies",PL[2],PL[1]])
		PL[0]=temp[0]
		PL[1]=temp[1]
		PL[2]=temp[2]
		temp=[]
	PL=resolveChild(PL)
	return PL


def eliminateIF(PL):
	''' Removes Implication. 
	Parameters:
	Input:
	a. PL - List supposedly containing Conditional operation as first element
	Output: List with IMPLIES converted '''
	
	if len(PL)<1:
		print ("Empty list to eliminateIF. ")
		return PL
	
	if PL[0]=="implies":
		# Solve for childrens first
		if isinstance(PL, list):
			length=len(PL)-1
			while length >0:
				if isinstance(PL[length], list):
					if len(PL[length])>0:
						PL[length]=resolveChild(PL[length])
				length-=1 
		PL[0]="or"
		PL[1]=["not",PL[1]]
	PL=resolveChild(PL)
	return PL
	

def eliminateDNEG(PL):
	''' Removes Double negation. 
	Parameters:
	Input:
	a. PL - List supposedly containing NOT operation as first element
	Output: List with NOT converted '''
	
	if len(PL)<1:
		print ("Empty list to eliminateDNEG. ")
		return PL
		
	if PL[0]!="not":
		return PL
	if isinstance(PL, list):
		if len(PL)>1:
			# Solve for child first
			if isinstance(PL[1], list):
				if len(PL[1])>0:
					PL[1]=resolveChild(PL[1])
	
		# De-MORGAN and double negation; loop through all childs
		if isinstance(PL[1], list):
			
			if PL[1][0]=="not":
				PL=PL[1][1]
			else:
				if PL[1][0]=="and":
					PL[1][0]="or"
				elif PL[1][0]=="or":
					PL[1][0]="and"
				length=len(PL[1])-1
				while length >0:
					if isinstance(PL[1][length], list):
						if len(PL[1][length])>0:
							PL[1][length]=resolveChild(["not",PL[1][length]])
					else:
						PL[1][length]=["not",PL[1][length]]
					length-=1
				PL=PL[1]
	return PL
	


def pushDisjunction(PL):
	''' Pushes disjunction downwards. 
	Parameters:
	Input:
	a. PL - List supposedly containing Conditional operation as first element
	Output: List with OR distributed over AND '''
	
	if len(PL)<1:
		print ("Empty list to pushDisjunction. ")
		return PL
		
	if PL[0]!="or":
		return PL
		
	
	if isinstance(PL, list):
		# Solve for childrens first
		length=len(PL)-1
		while length >0:
			if isinstance(PL[length], list):
				if len(PL[length])>0:
					PL[length]=resolveChild(PL[length])
			length-=1 
		
		# If more than 3 elements in OR, distribute ORs A | B | C | D =[ [  [A|B] | C ] | D ]
		if len(PL) >3:
			length=1
			while length< len(PL)-1:
				PL[1]=["or",PL[1],PL[2]]
				del PL[2]
				length+=1
		
		
		
		# No looping needed, since OR cannot have more than 2 elements now
		if len(PL)>2:
			if PL[1][0]=="and":
				temp=[]
				temp.append("and")
				length=1
				while length<len(PL[1]):
					temp.append(["or",PL[1][length],PL[2]])
					length+=1
				PL=[]
				PL.append(temp[0])
				length=1
				while length<len(temp):
					PL.append(pushDisjunction(temp[length]))
					length+=1
				temp=[]
				# Since this can create redundant ANDS
				PL=resolveChild(PL)
				
			elif PL[2][0]=="and":
				temp=[]
				temp.append("and")
				length=1
				while length<len(PL[2]):
					temp.append(["or",PL[2][length],PL[1]])
					length+=1
				PL=[]
				PL.append(temp[0])
				length=1
				while length<len(temp):
					PL.append(pushDisjunction(temp[length]))
					length+=1
				temp=[]
				# Since this can create redundant ANDS
				PL=resolveChild(PL)
		
		
		
		# Remove duplicates			
		temp=[]
		for el in PL:
			if el not in temp:
				temp.append(el)
		PL=temp	
		if len(PL)<3:
			if PL[0]=="or":
				PL=PL[1]
		
		# Call further methods
		if isinstance(PL, list):
			length=len(PL)-1
			while length >0:
				if isinstance(PL[length], list):
					if len(PL[length])>0:
						PL[length]=resolveChild(PL[length])
				length-=1
		
	return PL	
def removeDups_n(cnfForm):
	i=0
	temp=eval(str(cnfForm))
	check=[]
	while i < len(temp):
		check=temp[i]
		
		j=i+1
		while j < len(cnfForm):
			if sorted(check) == sorted (cnfForm[j]):
				del cnfForm[j]
			j+=1
		i+=1
	return cnfForm
			

def CNFconverter(arg):
	''' Reads input file containing propositional logic statements and returns CNF form of them in a file called sentences_CNF.txt
	Parameters: 
	Input:
	a. arg - Array containing options to run the script with. Third element must be the input file name
	Output: None '''
	
        args = len(arg)
        if args<3:
                print("Provide input file after script name.\nUsage: python CNFconverter.py -i inputfilename ")
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
                		with open("sentences_CNF.txt","w") as oFile:
		        		# Loop through the input file to read PL sentences (PL: Propositional Logic)
		        		while iterator < totLines:
		        			global done
						done=0
		        			currPL = eval(inputFile.readline())
		        			
		        			# Fucntion call to evaluate CNF
		        			try:
		        				cnfForm=getCNF(currPL)
		        				cnfForm=removeDups_n(cnfForm)
		        				if len(cnfForm) ==2:
		        					if cnfForm[0]=="and":
		        						cnfForm=cnfForm[1]
		        			except Exception as exc:
							traceback.print_exc()
							print(exc.args)
		        			print(cnfForm)
			        		oFile.write(str(cnfForm))
			        		oFile.write("\n")
		        			iterator+=1
                
                except Exception as exc:
                	traceback.print_exc()
                        print(exc.args)
                        

                                
        
if __name__ == "__main__":
   CNFconverter(sys.argv)
