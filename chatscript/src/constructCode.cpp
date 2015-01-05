﻿﻿﻿#include "common.h"

int impliedIf = ALREADY_HANDLED;	// testing context of an if
unsigned int withinLoop = 0;

static char* TestIf(char* ptr,FunctionResult& result)
{ //   word is a stream terminated by )
	//   if (%rand == 5 ) example of a comparison
	//   if (^QuerySubject()) example of a call or if (!QuerySubject())
	//   if ($var) example of existence
	//   if ('_3 == 5)  quoted matchvar
	//   if (1) what an else does
	char* word1 = AllocateBuffer();
	char* word2 = AllocateBuffer();
	char op[MAX_WORD_SIZE];
	unsigned int id;
	impliedIf = 1;
resume:
	ptr = ReadCompiledWord(ptr,word1);	//   the var or whatever
	bool invert = false;
	if (*word1 == '!') //   inverting, go get the actual
	{
		invert = true;
		// get the real token
		if (word1[1]) memmove(word1,word1+1,strlen(word1)); 
		else ptr = ReadCompiledWord(ptr,word1);	
	}
	ptr = ReadCompiledWord(ptr,op);		//   the test if any, or (for call or ) for closure or AND or OR
	bool call = false;
	if (*op == '(') // function call instead of a variable. but the function call might output a value which if not used, must be considered for failure
	{
		call = true;
		ptr -= strlen(word1) + 3; //   back up so output can see the fn name and space
		ChangeDepth(1,"TestIf");
		ptr = FreshOutput(ptr,word2,result,OUTPUT_ONCE|OUTPUT_KEEPSET); // word2 hold output value // skip past closing paren
		if (result & SUCCESSCODES) result = NOPROBLEM_BIT;	// legal way to terminate the piece with success at any  level
		if (trace & TRACE_OUTPUT) 
		{
			if (result & ENDCODES) id = Log(STDUSERTABLOG,"If %c%s ",(invert) ? '!' : ' ',word1);
			else if (*word1 == '1' && word1[1] == 0) id = Log(STDUSERTABLOG,"else ");
			else id = Log(STDUSERTABLOG,"if %c%s ",(invert) ? '!' : ' ',word1);
		}
		ChangeDepth(-1,"TestIf");
		ptr = ReadCompiledWord(ptr,op); // find out what happens next after function call
		if (!result && IsComparison(*op)) // didnt fail and followed by a relationship op, move output as though it was the variable
		{
			 strcpy(word1,word2); 
			 call = false;	// proceed normally
		}
		else if (result != NOPROBLEM_BIT) {;} // failed
		else if (!stricmp(word2,"0") || !stricmp(word2,"null") ) result = FAILRULE_BIT;	// treat 0 or null as failure along with actual failures
	}
		
	if (call){;} // call happened
	else if (IsComparison(*op)) //   a comparison test
	{
		ptr = ReadCompiledWord(ptr,word2);	
		result = HandleRelation(word1,op,word2,true,id);
		ptr = ReadCompiledWord(ptr,op);	//   AND, OR, or ) 
	}
	else //   existence of non-failure or any content
	{
		if (*word1 == '%' || *word1 == '_' || *word1 == '$' || *word1 == '@' || *word1 == '?' || (*word1 == '^' && IsDigit(word1[1])))
		{
			char* found;
			if (*word1 == '%') found = SystemVariable(word1,NULL);
			else if (*word1 == '_') found = wildcardCanonicalText[GetWildcardID(word1)];
			else if (*word1 == '$') found = GetUserVariable(word1);
			else if (*word1 == '?') found = (tokenFlags & QUESTIONMARK) ? (char*) "1" : (char*) "";
			else if (*word1 == '^') found = callArgumentList[atoi(word1+1)+fnVarBase]; // function var
			else found =  FACTSET_COUNT(GetSetID(word1)) ? (char*) "1" : (char*) "";
			if (trace & TRACE_OUTPUT) 
			{
				if (!*found) 
				{
					if (invert) id = Log(STDUSERTABLOG,"If !%s (null) ",word1);
					else id = Log(STDUSERTABLOG,"If %s (null) ",word1);
				}
				else 
				{
					if (invert) id = Log(STDUSERTABLOG,"If !%s (%s) ",word1,found);
					else id = Log(STDUSERTABLOG,"If %s (%s) ",word1,found);
				}
			}
			if (!*found) result = FAILRULE_BIT;
			else result = NOPROBLEM_BIT;
		}
		else  //  its a constant of some kind 
		{
			if (trace & TRACE_OUTPUT) 
			{
				if (result & ENDCODES) id = Log(STDUSERTABLOG,"If %c%s ",(invert) ? '!' : ' ',word1);
				else if (*word1 == '1' && word1[1] == 0) id = Log(STDUSERTABLOG,"else ");
				else id = Log(STDUSERTABLOG,"if %c%s ",(invert) ? '!' : ' ',word1);
			}
			ptr -= strlen(word1) + 3; //   back up to process the word and space
			ptr = FreshOutput(ptr,word2,result,OUTPUT_ONCE|OUTPUT_KEEPSET) + 2; //   returns on the closer and we skip to accel
		}
	}
	if (invert) result = (result & ENDCODES) ? NOPROBLEM_BIT : FAILRULE_BIT; 
	
	if (*op == 'a') //   AND - compiler validated it
	{
		if (!(result & ENDCODES)) 
		{
			if (trace & TRACE_OUTPUT) id = Log(STDUSERLOG," AND ");
			goto resume;
			//   If he fails (result is one of ENDCODES), we fail
		}
		else 
		{
			if (trace & TRACE_OUTPUT) id = Log(STDUSERLOG," ... ");
		}
	}
	else if (*op == 'o') //  OR
	{
		if (!(result & ENDCODES)) 
		{
			if (trace & TRACE_OUTPUT) id = Log(STDUSERLOG," ... ");
			result = NOPROBLEM_BIT;
		}
		else 
		{
			if (trace & TRACE_OUTPUT) id = Log(STDUSERLOG," OR ");
			goto resume;
		}
	}
	if (*(ptr-2) != ')') // recover end of it .. ) space jump code
	{
		char* squiggle = strchr(ptr,'{'); // here is start of the branch
		if (squiggle)
		{
			while (*--squiggle != ')') {;} // back up to close of paren
			ptr = squiggle + 2;
		}
	}


	FreeBuffer();
	FreeBuffer();
	if (trace & TRACE_OUTPUT &&  (result & ENDCODES)) Log(id,"%s\r\n", "FAIL-if");
	impliedIf = ALREADY_HANDLED;
	return ptr;
}

char* HandleIf(char* ptr, char* buffer,FunctionResult& result)
{
	// If looks like this: ^^if ( _0 == null ) 00m{ this is it } 00G else ( 1 ) 00q { this is not it } 004 
	// a nested if would be ^^if ( _0 == null ) 00m{ ^^if ( _0 == null ) 00m{ this is it } 00G else ( 1 ) 00q { this is not it } 004 } 00G else ( 1 ) 00q { this is not it } 004
	// after a test condition is code to jump to next test branch when condition fails
	// after { }  chosen branch is offset to jump to end of if
	while (ALWAYS) //   do test conditions until match
	{
		//   Perform TEST condition
		ptr = TestIf(ptr+2,result); //   skip (space, returns on accelerator
						
		//   perform SUCCESS branch and then end if
		if (!(result & ENDCODES)) //   IF test success - we choose this branch
		{
			ChangeDepth(1,"HandleIf");
			ChangeDepth(1,"HandleIf");
			ptr = Output(ptr+5,buffer,result); //   skip accelerator-3 and space and { and space - returns on next useful token
			ChangeDepth(-1,"HandleIf");
			ptr += Decode(ptr);	//   offset to end of if entirely
			ChangeDepth(-1,"HandleIf");
			break;
		}
		else 
			result = NOPROBLEM_BIT;		//   test result is not the IF result
	
		//   On fail, move to next test
		ptr += Decode(ptr);
		if (strncmp(ptr,"else ",5))  break; //   not an ELSE, the IF is over. 
		ptr += 5; //   skip over ELSE space, aiming at the (of the condition
	}
	return ptr;
} 

char* HandleLoop(char* ptr, char* buffer, FunctionResult &result)
{
	unsigned int oldIterator = currentIterator;
	currentIterator = 0;
	char* word = AllocateBuffer();
	ptr = ReadCommandArg(ptr+2,word,result)+2; //   get the loop counter value and skip closing ) space 
	char* endofloop = ptr + (size_t) Decode(ptr);
	int counter = atoi(word);
	FreeBuffer();
	if (result & ENDCODES) return endofloop;

	++withinLoop;

	ptr += 5;	//   skip jump + space + { + space
	if (counter > 1000 || counter < 0) counter = 1000; //   LIMITED
	while (counter-- > 0)
	{
		ChangeDepth(2,"HandleLoop");
		if (trace & TRACE_OUTPUT) Log(STDUSERTABLOG,"loop (%d)\r\n",counter+1);
		FunctionResult result1;
		Output(ptr,buffer,result1,OUTPUT_LOOP);
		buffer += strlen(buffer);
		ChangeDepth(-2,"HandleLoop");
		if (result1 & ENDCODES) 
		{
			result = (FunctionResult)( (result1 & (ENDRULE_BIT | FAILRULE_BIT)) ? NOPROBLEM_BIT : (result1 & ENDCODES) );  // rule level terminates only the loop
			break;//   potential failure if didnt add anything to buffer
		}
	}
	if (trace & TRACE_OUTPUT) Log(STDUSERTABLOG,"end of loop\r\n");
	--withinLoop;

	currentIterator = oldIterator;
	return endofloop;
}  

FunctionResult HandleRelation(char* word1,char* op, char* word2,bool output,unsigned int& id)
{ //   word1 and word2 are RAW, ready to be evaluated.
	char* val1 = AllocateBuffer();
	char* val2 = AllocateBuffer();
	WORDP D;
	WORDP D1;
	WORDP D2;
	int64 v1 = 0;
	int64 v2 = 0;
	FunctionResult result,val1Result;
	FreshOutput(word1,val1,result,OUTPUT_ONCE|OUTPUT_KEEPSET|OUTPUT_NOCOMMANUMBER); // 1st arg
	val1Result = result;
	if (word2 && *word2) FreshOutput(word2,val2,result,OUTPUT_ONCE|OUTPUT_KEEPSET|OUTPUT_NOCOMMANUMBER); // 2nd arg
	result = FAILRULE_BIT;
	if (!stricmp(val1,"null") ) *val1 = 0;
	if (!stricmp(val2,"null") ) *val2 = 0;
	if (!op)
	{
		if (val1Result & ENDCODES); //   explicitly failed
		else if (*val1) result = NOPROBLEM_BIT;	//   has some value
	}
	else if (*op == '?' || op[1] == '?') // ? and !? 
	{
		if (*word1 == '\'') ++word1; // ignore the quote since we are doing positional
		if (*word1 == '_') // try for precomputed match from memorization
		{
			unsigned int index = GetWildcardID(word1);
			index = WILDCARD_START(wildcardPosition[index]);
			D = FindWord(val2);
			if (index && D)
			{
				unsigned int junk,junk1;
				if (GetNextSpot(D,index-1,junk,junk1) == index) result = NOPROBLEM_BIT; // otherwise failed and we would have known
			}
			if (result == FAILRULE_BIT) // laborious match try now
			{
				D1 = FindWord(val1);
				if (D1 && D)
				{
					NextInferMark();
					if (SetContains(MakeMeaning(D),MakeMeaning(D1))) result = NOPROBLEM_BIT;
				}
			}
			if (*op == '!') result = (result != NOPROBLEM_BIT) ? NOPROBLEM_BIT : FAILRULE_BIT;
		}
		else // laborious.
		{
			D1 = FindWord(val1);
			D2 = FindWord(val2);
			if (D1 && D2)
			{
				NextInferMark();
				if (SetContains(MakeMeaning(D2),MakeMeaning(D1))) result = NOPROBLEM_BIT;
			}
			if (result != NOPROBLEM_BIT)
			{
				char* verb = GetInfinitive(val1,true);
				if (verb && stricmp(verb,val1))
				{
					D1 = FindWord(verb);
					if (D1 && D2)
					{
						NextInferMark();
						if (SetContains(MakeMeaning(D2),MakeMeaning(D1))) result = NOPROBLEM_BIT;
					}
				}
			}
			if (result != NOPROBLEM_BIT)
			{
				char* noun = GetSingularNoun(val1,true,true);
				if (noun && stricmp(noun,val1))
				{
					D1 = FindWord(noun);
					if (D1 && D2)
					{
						NextInferMark();
						if (SetContains(MakeMeaning(D2),MakeMeaning(D1))) result = NOPROBLEM_BIT;
					}
				}
			}
			if (*op == '!') result = (result != NOPROBLEM_BIT) ? NOPROBLEM_BIT : FAILRULE_BIT;
		}
	}
	else //   boolean tests
	{
		// convert null to numeric operator for < or >  -- but not for equality
		if (!*val1 && IsDigit(*val2) && IsNumber(val2) && (*op == '<' || *op == '>')) strcpy(val1,"0");
		else if (!*val2 && IsDigit(*val1) && IsNumber(val1) && (*op == '<' || *op == '>')) strcpy(val2,"0");

		if (!IsDigitWord(val1) || !IsDigitWord(val2)) //   non-numeric string compare - bug, can be confused if digit starts text string
		{
			char* arg1 = val1;
			char* arg2 = val2;
			if (*arg1 == '"')
			{
				size_t len = strlen(arg1);
				if (arg1[len-1] == '"') // remove STRING markers
				{
					arg1[len-1] = 0;
					++arg1;
				}
			}
			if (*arg2 == '"')
			{
				size_t len = strlen(arg2);
				if (arg2[len-1] == '"') // remove STRING markers
				{
					arg2[len-1] = 0;
					++arg2;
				}
			}			
			if (*op == '!') result = (stricmp(arg1,arg2)) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else if (*op == '=') result = (!stricmp(arg1,arg2)) ? NOPROBLEM_BIT: FAILRULE_BIT;
			else result = FAILRULE_BIT;
		}
		//   handle float ops
		else if ((strchr(val1,'.') && val1[1]) || (strchr(val2,'.') && val2[1])) // at least one arg is float
		{
			char* comma = 0; 
			while ((comma = strchr(val1,',')))  memmove(comma,comma+1,strlen(comma+1)); // remove embedded commas
			while ((comma = strchr(val2,',')))  memmove(comma,comma+1,strlen(comma+1)); // remove embedded commas
			float v1 = (float) atof(val1);
			float v2 = (float) atof(val2);
			if (*op == '=') result = (v1 == v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else if (*op == '<') 
			{
				if (!op[1]) result =  (v1 < v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
				else result =  (v1 <= v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			}
			else if (*op == '>') 
			{
				if (!op[1]) result =  (v1 > v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
				else result =  (v1 >= v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			}
			else if (*op == '!') result = (v1 != v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else result = FAILRULE_BIT;
		}
		else //   int compare
		{
			char* comma =  0; // pretty number?
			while ((comma = strchr(val1,',')))  memmove(comma,comma+1,strlen(comma+1));
			while ((comma = strchr(val2,',')))  memmove(comma,comma+1,strlen(comma+1));
			ReadInt64(val1,v1);
			ReadInt64(val2,v2);
			if (strchr(val1,',') && strchr(val2,',')) // comma numbers
			{
				size_t len1 = strlen(val1);
				size_t len2 = strlen(val2);
				if (len1 != len2) result = FAILRULE_BIT;
				else if (strcmp(val1,val2)) result = FAILRULE_BIT;
				else result = NOPROBLEM_BIT;
				if (*op == '!') result =  (result == NOPROBLEM_BIT) ? FAILRULE_BIT : NOPROBLEM_BIT;
				else if (*op != '=') ReportBug("Op not implemented for comma numbers %s",op)
			}
			else if (*op == '=') result =  (v1 == v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else if (*op == '<') 
			{
				if (!op[1]) result =  (v1 < v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
				else result =  (v1 <= v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			}
			else if (*op == '>') 
			{
				if (!op[1]) result =  (v1 > v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
				else result =  (v1 >= v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			}
			else if (*op == '!') result =  (v1 != v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else if (*op == '&') result =  (v1 & v2) ? NOPROBLEM_BIT : FAILRULE_BIT;
			else result =  FAILRULE_BIT;
		}
	}
	if (trace & TRACE_OUTPUT && output) 
	{
		char x[MAX_WORD_SIZE];
		char y[MAX_WORD_SIZE];
		*x = *y = 0;
		if (*op == '&') 
		{
#ifdef WIN32
			sprintf(x,"0x%016I64x",v1);
			sprintf(y,"0x%016I64x",v2);
#else
			sprintf(x,"0x%016llx",v1);
			sprintf(y,"0x%016llx",v2); 
#endif		
		}
		if (!stricmp(word1,val1)) 
		{
			if (*word1) Log(STDUSERTABLOG,"if %s %s ",(*x) ? x : word1,op); // no need to show value
			else Log(STDUSERTABLOG,"if null %s ",op);
		}
		else if (!*val1) Log(STDUSERTABLOG,"if  %s (null) %s ",word1,op);
		else if (*op == '&')  Log(STDUSERTABLOG,"if  %s (%s) %s ",word1,x,op);
		else Log(STDUSERTABLOG,"if  %s (%s) %s ",word1,val1,op);

		if (!strcmp(word2,val2)) 
		{
			if (*val2) id = Log(STDUSERLOG," %s ",(*y) ? y : word2); // no need to show value
			else id = Log(STDUSERLOG," null "); 
		}
		else if (!*val2)  id = Log(STDUSERLOG," %s (null) ",word2);
		else if (*op == '&') id = Log(STDUSERLOG," %s (%s) ",word2,y);
		else id = Log(STDUSERLOG," %s (%s) ",word2,val2);
	}
	else if (trace & TRACE_PATTERN && !output) 
	{
		if (!stricmp(word1,val1))
		{
			if (*word1) Log(STDUSERLOG,"%s %s ",word1,op); // dont need to show value
			else Log(STDUSERLOG,"null %s ",op); 
		}
		else if (!*val1) Log(STDUSERTABLOG,"if  %s (null) %s  ",word1,op);
		else  Log(STDUSERLOG,"%s (%s) %s ",word1,val1,op);
		if (!(strcmp(word2,val2))) 
		{
			if (*val2)  id = Log(STDUSERLOG,"%s ",word2); // dont need to show value
			else id = Log(STDUSERLOG,"null "); 
		}
		else if (!*val2)  id = Log(STDUSERLOG," %s (null) ",word2);
		else  id = Log(STDUSERLOG," %s (%s) ",word2, val2);
	}

	FreeBuffer();
	FreeBuffer();
	return result;
}
