﻿﻿﻿// variableSystem.cpp - manage user variables ($variables)

#include "common.h"

#ifdef INFORMATION
There are 5 kinds of variables.
	1. User variables beginning wih $ (regular and transient which begin with $$)
	2. Wildcard variables beginning with _
	3. Fact sets beginning with @ 
	4. Function variables beginning with ^ 
	5. System variables beginning with % 
#endif

int impliedSet = ALREADY_HANDLED;	// what fact set is involved in operation
int impliedWild = ALREADY_HANDLED;	// what wildcard is involved in operation

unsigned int wildcardIndex = 0;
char wildcardOriginalText[MAX_WILDCARDS+1][MAX_WORD_SIZE];  // spot wild cards can be stored
char wildcardCanonicalText[MAX_WILDCARDS+1][MAX_WORD_SIZE];  // spot wild cards can be stored
unsigned int wildcardPosition[MAX_WILDCARDS+1]; // spot it started and ended in sentence

//   list of active variables needing saving

#define MAX_USERVAR_SIZE 999
WORDP userVariableList[MAX_USER_VARS];	// variables read in from user file
WORDP botVariableList[MAX_USER_VARS];	// variables created by bot load
static char* baseVariableValues[MAX_USER_VARS];
unsigned int userVariableIndex;
unsigned int botVariableIndex;

void InitVariableSystem()
{
	botVariableIndex = userVariableIndex = 0;
}

int GetWildcardID(char* x) // wildcard id is "_10" or "_3"
{
	if (!IsDigit(x[1])) return -1;
	unsigned int n = x[1] - '0';
	char c = x[2];
	if (IsDigit(c)) n =  (n * 10) + (c - '0');
	return (n > MAX_WILDCARDS) ? -1 : n; 
}

static void CompleteWildcard()
{
	WORDP D = FindWord(wildcardCanonicalText[wildcardIndex]);
	if (D && D->properties & D->internalBits & UPPERCASE_HASH)  // but may not be found if original has plural or such or if uses _
	{
		strcpy(wildcardCanonicalText[wildcardIndex],D->word);
	}

    ++wildcardIndex;
	if (wildcardIndex > MAX_WILDCARDS) wildcardIndex = 0; 
}

void SetWildCard(unsigned int start, unsigned int end)
{
	if (end < start) end = start;				// matched within a token
	if (end > wordCount) end = wordCount;
    wildcardPosition[wildcardIndex] = start | (end << 16);
    *wildcardOriginalText[wildcardIndex] = 0;
    *wildcardCanonicalText[wildcardIndex] = 0;
	if (start == 0 || wordCount == 0 || (end == 0 && start != 1) ) // null match, like _{ .. }
	{
		++wildcardIndex;
		if (wildcardIndex > MAX_WILDCARDS) wildcardIndex = 0; 
	}
	else // did match
	{
		// concatenate the match value
		bool started = false;
		for (unsigned int i = start; i <= end; ++i)
		{
			char* word = wordStarts[i];
			// if (*word == ',') continue; // DONT IGNORE COMMAS, needthem
			if (started) 
			{
				strcat(wildcardOriginalText[wildcardIndex]," ");
				strcat(wildcardCanonicalText[wildcardIndex]," ");
			}
			else started = true;
			strcat(wildcardOriginalText[wildcardIndex],word);
			if (wordCanonical[i]) strcat(wildcardCanonicalText[wildcardIndex],wordCanonical[i]);
			else 
				strcat(wildcardCanonicalText[wildcardIndex],word);
		}
 		if (trace & TRACE_OUTPUT) Log(STDUSERLOG,"_%d=%s/%s ",wildcardIndex,wildcardOriginalText[wildcardIndex],wildcardCanonicalText[wildcardIndex]);
		CompleteWildcard();
	}
}

void SetWildCardIndexStart(unsigned int index)
{
	 wildcardIndex = index;
}

void SetWildCard(char* value, char* canonicalValue,const char* index,unsigned int position)
{
	// adjust values to assign
	if (!value) value = "";
	if (!canonicalValue) canonicalValue = "";
    if (strlen(value) > MAX_USERVAR_SIZE) 
	{
		value[MAX_USERVAR_SIZE] = 0;
		ReportBug("long original value %s",value)
	}
     if (strlen(canonicalValue) > MAX_USERVAR_SIZE) 
	{
		canonicalValue[MAX_USERVAR_SIZE] = 0;
		ReportBug("long canonnical value %s",value)
	}
	while (value[0] == ' ') ++value; 
    while (canonicalValue && canonicalValue[0] == ' ') ++canonicalValue;

	// store the values
	if (index) wildcardIndex = GetWildcardID((char*)index); 
    strcpy(wildcardOriginalText[wildcardIndex],value);
    strcpy(wildcardCanonicalText[wildcardIndex],(canonicalValue) ? canonicalValue : value);
    wildcardPosition[wildcardIndex] = position | (position << 16); 
  
	CompleteWildcard();
}

char* GetwildcardText(unsigned int i, bool canon)
{
	if (i > MAX_WILDCARDS) return "";
    return canon ? wildcardCanonicalText[i] : wildcardOriginalText[i];
}

char* GetUserVariable(const char* word)
{
	WORDP D = FindWord((char*) word,0,LOWERCASE_LOOKUP);
	if (!D)  return "";	//   no such variable

	char* item = D->w.userValue;
    if (!item)  return ""; // null value
    return (*item == '&') ? (item + 1) : item; //   value is quoted or not
 }

void ClearUserVariableSetFlags()
{
	for (unsigned int i = 0; i < userVariableIndex; ++i) RemoveInternalFlag(userVariableList[i],VAR_CHANGED);
}

void ShowChangedVariables()
{
	for (unsigned int i = 0; i < userVariableIndex; ++i) 
	{
		if (userVariableList[i]->internalBits & VAR_CHANGED)
		{
			char* value = userVariableList[i]->w.userValue;
			if (value && *value) Log(1,"%s = %s\r\n",userVariableList[i]->word,value);
			else Log(1,"%s = null\r\n",userVariableList[i]->word);
		}
	}
}

static WORDP CreateUserVariable(const char* var, char* value)
{
	char word[MAX_WORD_SIZE];
	MakeLowerCopy(word,(char*)var);
    WORDP D = StoreWord(word);				// find or create the var.
	if (!D) return NULL; // ran out of memory
    if (!(D->internalBits & VAR_CHANGED))	// not changed already this volley
    {
        userVariableList[userVariableIndex++] = D;
        if (userVariableIndex == MAX_USER_VARS) // if too many variables, discard one (wont get written)
        {
            --userVariableIndex;
            ReportBug("too many user vars at %s value: %s\r\n",var,value);
        }
		D->w.userValue = NULL; 
		AddInternalFlag(D,VAR_CHANGED);
	}
	if (planning && !documentMode) // handle undoable assignment (cannot use text sharing as done in document mode)
	{
		if (D->w.userValue == NULL) SpecialFact(MakeMeaning(D),(MEANING)1,0);
		else SpecialFact(MakeMeaning(D),(MEANING) (D->w.userValue - stringBase ),0);
	}
	D->w.userValue = value; 
	return D;
}

void SetUserVariable(const char* var, char* word)
{
	// adjust value
	if (word) // has a nonnull value?
	{
		if (!*word || !stricmp(word,"null") ) word = NULL; // really is null
		else //   some value 
		{
			size_t len = strlen(word);
			if (len > MAX_USERVAR_SIZE) word[MAX_USERVAR_SIZE + 1] = 0; // limit on user vars same as match vars
			if (documentMode) // try to save space
			{
				WORDP X = FindWord(word);
				if (X && !strcmp(word,X->word)) word = X->word; // has same value
				else  word = AllocateString(word);
			}
			else word = AllocateString(word);
			if (!word) return;
		}
	}
	WORDP D = CreateUserVariable(var,word);
	if (!D) return;
	// tokencontrol changes are noticed by the engine
	if (!strcmp(var,"$token")) 
	{
		int64 val = 0;
		if (word && *word) ReadInt64(word,val);
		else val = (DO_INTERJECTION_SPLITTING|DO_SUBSTITUTE_SYSTEM|DO_NUMBER_MERGE|DO_PROPERNAME_MERGE|DO_SPELLCHECK);
		tokenControl = val;
	}
	if (trace == TRACE_VARIABLESET) Log(STDUSERLOG,"Var: %s -> %s\r\n",D->word,word);
}

void Add2UserVariable(char* var, char* moreValue,char minusflag,char* originalArg)
{
	// get original value
	char* oldValue;
    if (*var == '_') oldValue = GetwildcardText(GetWildcardID(var),true); // onto a wildcard
	else if (*var == '$') oldValue = GetUserVariable(var); // onto user variable
	else if (*var == '^') oldValue = callArgumentList[atoi(var+1)+fnVarBase]; // onto function argument
	else return; // illegal

	// get augment value
	if (*moreValue == '_') moreValue = GetwildcardText(GetWildcardID(moreValue),true); 
	else if (*moreValue == '$') moreValue = GetUserVariable(moreValue); 
	else if (*moreValue == '^') moreValue = callArgumentList[atoi(moreValue+1)+fnVarBase];

	// perform numeric op
	bool floating = false;
	if (strchr(oldValue,'.') || strchr(moreValue,'.') ) floating = true; 
	char result[MAX_WORD_SIZE];
	if (minusflag == '<')
	{
		int xx =0;
	}
	if (trace & TRACE_OUTPUT) Log(STDUSERLOG,"%s %c %s(%s/0x%x) ",var,minusflag,originalArg,moreValue,atoi(moreValue));

    if (floating)
    {
        float newval = (float)atof(oldValue);
		float more = (float)atof(moreValue);
        if (minusflag == '-') newval -= more;
        else if (minusflag == '*') newval *= more;
        else if (minusflag == '/') newval /= more;
		else if (minusflag == '%') 
		{
			int64 ivalue = (int64) newval;
			int64 morval = (int64) more;
			newval = (float) (ivalue % morval);
		}
        else newval += more;
        sprintf(result,"%1.2f",newval);
    }
    else
    {
		int64 newval;
		ReadInt64(oldValue,newval);
		int64 more;
		ReadInt64(moreValue,more);
        if (minusflag == '-') newval -= more;
        else if (minusflag == '*') newval *= more;
        else if (minusflag == '/') 
		{
			if (more == 0) 
				return; // cannot divide by 0
			newval /= more;
		}
        else if (minusflag == '%') newval %= more;
        else if (minusflag == '|') newval |= more;
        else if (minusflag == '&') newval &= more;
        else if (minusflag == '^') newval ^= more;
        else if (minusflag == '<') newval <<= more;
        else if (minusflag == '>') newval >>= more;
       else newval += more;
#ifdef WIN32
		 sprintf(result,"%I64d",newval); 
#else
		 sprintf(result,"%lld",newval); 
#endif        
    }

	// store result back
	if (*var == '_')  SetWildCard(result,result,var,0); 
	else if (*var == '$') SetUserVariable(var,result);
	else if (*var == '^') strcpy(callArgumentList[atoi(var+1)+fnVarBase],result); 
	if (trace & TRACE_OUTPUT) Log(STDUSERLOG,"=> %s/0x%x   ",result,atoi(result));
}

void ReestablishBotVariables() // refresh bot variables
{
	for (unsigned int i = 0; i < botVariableIndex; ++i) botVariableList[i]->w.userValue = baseVariableValues[i];
}

void ClearBotVariables()
{
	botVariableIndex = 0;
}

void NoteBotVariables() // system defined variables
{
	if (userVariableIndex) printf("Read %s Variables\r\n",StdIntOutput(userVariableIndex));
	botVariableIndex = userVariableIndex;
	for (unsigned int i = 0; i < botVariableIndex; ++i)
	{
		botVariableList[i] = userVariableList[i];
		baseVariableValues[i] = botVariableList[i]->w.userValue;
	}
	ClearUserVariables();
}

void ClearUserVariables(char* above)
{
	unsigned int count = userVariableIndex;
	while (count)
	{
		WORDP D = userVariableList[--count]; // 0 based
		if (D->w.userValue < above)
		{	
			D->w.userValue = NULL;
			RemoveInternalFlag(D,VAR_CHANGED);
			userVariableList[count] = userVariableList[--userVariableIndex]; // pack in if appropriate
		}
 	}
	if (!above) userVariableIndex = 0;
}

void DumpVariables()
{
	char* value;
	for (unsigned int i = 0; i < botVariableIndex; ++i) 
	{
		value = botVariableList[i]->w.userValue;
		if (value && *value)  Log(STDUSERLOG,"  bot variable: %s = %s\r\n",botVariableList[i],value);
	}

	for (unsigned int i = 0; i < userVariableIndex; ++i)
	{
		WORDP D = userVariableList[i];
		value = D->w.userValue;
		if (value && *value)  
		{
			if (!stricmp(D->word,"$token"))
			{
				Log(STDUSERLOG,"  variable: decoded %s = ",D->word);
				int64 val;
				ReadInt64(value,val);
				DumpTokenControls(val);
				Log(STDUSERLOG,"\r\n");
			}
			else Log(STDUSERLOG,"  variable: %s = %s\r\n",D->word,value);
		}
	}
}

char* PerformAssignment(char* word,char* ptr,FunctionResult &result)
{// assign to and from  $var, _var, ^var, @set, and %sysvar
    char op[MAX_WORD_SIZE];
	ChangeDepth(2,"PerformAssignment");
	char* word1 = AllocateBuffer();
	FACT* F = currentFact;
	currentFact = NULL;					// did createfact  creat OR find
	int oldImpliedSet = impliedSet;		// in case nested calls happen
	int oldImpliedWild = impliedWild;	// in case nested calls happen
    int assignFromWild = ALREADY_HANDLED;
	result = NOPROBLEM_BIT;
	impliedSet = (*word == '@') ? GetSetID(word) : ALREADY_HANDLED;			// if a set save location
	impliedWild = (*word == '_') ? GetWildcardID(word) : ALREADY_HANDLED;	// if a wildcard save location
	int setToImply = impliedSet;
	int setToWild = impliedWild;

	if (*word == '^') // function variable must be changed to actual value. can never replace a function variable binding  --- CHANGED nowadays are allowed to write on the function binding itself (done outside here)
	{
		ReadShortCommandArg(word,word1,result,OUTPUT_NOTREALBUFFER);
		if (result & ENDCODES) goto exit; // failed
		strcpy(word,word1);
	}

	// Get assignment operator
    ptr = ReadCompiledWord(ptr,op); // assignment operator = += -= /= *= %= 
	if (trace & TRACE_OUTPUT) Log(STDUSERTABLOG,"%s %s ",word,op);
	char original[MAX_WORD_SIZE];
	ReadCompiledWord(ptr,original);

	// get the from value
	assignFromWild =  (*ptr == '_' && IsDigit(ptr[1])) ? GetWildcardID(ptr)  : -1;
	if (assignFromWild >= 0 && *word == '_') ptr = ReadCompiledWord(ptr,word1); // assigning from wild to wild. Just copy across
	else
	{
		ptr = ReadCommandArg(ptr,word1,result,OUTPUT_NOTREALBUFFER); // need to see null assigned
		if (*word1 == '#') // substitute a constant? user type-in :set command for example
		{
			uint64 n = FindValueByName(word1+1);
			if (!n) n = FindValue2ByName(word1+1);
			if (n) 
			{
#ifdef WIN32
				sprintf(word1,"%I64d",(long long int) n); 
#else
				sprintf(word1,"%lld",(long long int) n); 
#endif	
			}
		}
		if (result & ENDCODES) goto exit;
		// A fact was created but not used up by retrieving some field of it. Convert to a reference to fact.
		if (currentFact && setToImply == impliedSet && setToWild == impliedWild) sprintf(word1,"%d",currentFactIndex());
		if (!currentFact) currentFact = F; // revert current fact to what it was before now
	}
   	if (!stricmp(word1,"null")) *word1 = 0;

	//   now sort out who we are assigning into and if its arithmetic or simple assign

	if (*word == '@')
	{
		if (!*word1 && *op == '=') // null assign to set as a whole
		{
			SET_FACTSET_COUNT(impliedSet,0);
			factSetNext[impliedSet] = 0;
		}
		else if (*word1 == '@') // set to set operator
		{
			FACT* F;
			unsigned int rightSet = GetSetID(word1);
			if (rightSet == ILLEGAL_FACTSET) 
			{
				result = FAILRULE_BIT;
				return ptr;
			}
			unsigned int rightCount =  FACTSET_COUNT(rightSet);
			unsigned int impliedCount =  FACTSET_COUNT(impliedSet); 
			if (*op == '+') while (rightCount) AddFact(impliedSet,factSet[rightSet][rightCount--]); // add set to set preserving order
			else if (*op == '-') // remove from set
			{
				for (unsigned int i = 1; i <= rightCount; ++i) factSet[rightSet][i]->flags |= MARKED_FACT; // mark right facts
				for (unsigned int i = 1; i <= impliedCount; ++i) // erase from the left side
				{ 
					F = factSet[impliedSet][i];
					if (F->flags & MARKED_FACT)
					{
						memmove(&factSet[impliedSet][i],&factSet[impliedSet][i+1], (impliedCount - i)* sizeof(FACT*));
						--impliedCount; // new end count
						--i; // redo loop at this point
					}
				}
				for (unsigned int i = 1; i <= rightCount; ++i) factSet[rightSet][i]->flags ^= MARKED_FACT; // erase marks
				SET_FACTSET_COUNT(impliedSet,impliedCount);
			}
			else if (*op == '=') memmove(&factSet[impliedSet][0],&factSet[rightSet][0], (rightCount+1) * sizeof(FACT*)); // assigned from set
			else result = FAILRULE_BIT;
		}
		else if (IsDigit(*word1) || !*word1) // fact index (or null fact) to set operators 
		{
			unsigned int index;
			ReadInt(word1,index);
			FACT* F = Index2Fact(index);
			unsigned int impliedCount =  FACTSET_COUNT(impliedSet); 
			if (*op == '+') AddFact(impliedSet,F); // add to set
			else if (*op == '-') // remove from set
			{
				if (F) F->flags |= MARKED_FACT;
				for (unsigned int i = 1; i <= impliedCount; ++i) // erase from the left side
				{ 
					FACT* G = factSet[impliedSet][i];
					if ((G && G->flags & MARKED_FACT) || (!G && !F))
					{
						memmove(&factSet[impliedSet][i],&factSet[impliedSet][i+1], (impliedCount - i)* sizeof(FACT*) );
						--impliedCount;
						--i;
					}
				}
				SET_FACTSET_COUNT(impliedSet,impliedCount);
				F->flags ^= MARKED_FACT;
			}
			else if (*op == '=') // assign to set (cant do this with null because it erases the set)
			{
				SET_FACTSET_COUNT(impliedSet,0);
				AddFact(impliedSet,F);
			}
			else result = FAILRULE_BIT;
		}
		if (FACTSET_COUNT(impliedSet) == 0) factSetNext[impliedSet] = 0; // set going empty requires a reset of next ptr
		impliedSet = ALREADY_HANDLED;
	}
	else if (IsArithmeticOperator(op)) Add2UserVariable(word,word1,*op,original);
	else if (*word == '_') //   assign to wild card
	{
		if (impliedWild != ALREADY_HANDLED) // no one has actually done the assignnment yet
		{
			if (assignFromWild >= 0) // full tranfer of data
			{
				SetWildCard(wildcardOriginalText[assignFromWild],wildcardCanonicalText[assignFromWild],word,0); 
				wildcardPosition[GetWildcardID(word)] =  wildcardPosition[assignFromWild];
			}
			else SetWildCard(word1,word1,word,0); 
		}
	}
	else if (*word == '$') SetUserVariable(word,word1);
	else if (*word == '\'' && word[1] == '$') SetUserVariable(word+1,word1); // '$xx = value  -- like passed thru as argument
	else if (*word == '%') SystemVariable(word,word1); 
	else // if (*word == '^') // cannot touch a function argument, word, or number
	{
		result = FAILRULE_BIT;
		goto exit;
	}

	//  followup arithmetic operators?
	while (ptr && IsArithmeticOperator(ptr))
	{
		ptr = ReadCompiledWord(ptr,op);
		ReadCompiledWord(ptr,original);
		ptr = ReadCommandArg(ptr,word1,result); 
		if (!stricmp(word1,word)) 
		{
			result = FAILRULE_BIT;
			Log(STDUSERLOG,"variable assign %s has itself as a term\r\n",word);
		}
		if (result & ENDCODES) goto exit; // failed next value
		Add2UserVariable(word,word1,*op,original);
	}

	// debug
	if (trace & TRACE_OUTPUT)
	{
		char* answer = AllocateBuffer();
		FunctionResult result;
		logUpdated = false;
		if (*word == '$') strcpy(answer,GetUserVariable(word));
		else if (*word == '_') strcpy(answer,wildcardOriginalText[GetWildcardID(word)]);
		else if (*word == '@') sprintf(answer,"[%d]",FACTSET_COUNT(GetSetID(word))); // show set count
		else FreshOutput(word,answer,result,OUTPUT_SILENT,MAX_WORD_SIZE);
		if (!*answer) 
		{
			if (logUpdated) Log(STDUSERTABLOG,"=> null  end-assign\r\n");
			else Log(1,"null \r\n");
		}
		else if (logUpdated) Log(STDUSERTABLOG,"=> %s  end-assign\r\n",answer);
		else Log(1," %s  \r\n",answer);
		FreeBuffer();
	}

exit:
	FreeBuffer();
	ChangeDepth(-2,"PerformAssignment");
	impliedSet = oldImpliedSet;
	impliedWild = oldImpliedWild;
	return ptr;
}
