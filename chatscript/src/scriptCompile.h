﻿﻿﻿#ifndef _SCRIPTCOMPILEH_
#define _SCRIPTCOMPILEH_
#ifdef INFORMATION
Copyright (C) 2011-2014 by Bruce Wilcox

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#endif

#define NO_SPELL 1		// test nothing
#define PATTERN_SPELL 1	// test pattern words for validity
#define OUTPUT_SPELL 2	// test output words for validity

extern uint64 buildID; // build 0 or build 1
extern bool compiling;
extern bool patternContext;
extern char* newBuffer;
extern uint64 grade;

void ScriptError();
void EraseTopicFiles(uint64 build);
void InitScriptSystem();

#ifndef DISCARDSCRIPTCOMPILER

char* ReadDisplayOutput(char* ptr,char* buffer);
  
void ReadTopicFiles(char* name,uint64 build, int spell);
char* ReadPattern(char* ptr, FILE* in, char* &data,bool macro);
char* ReadOutput(char* ptr, FILE* in,char* &data,char* rejoinders,char* existingRead = NULL,WORDP call = NULL);
char* CompileString(char* ptr);
void ScriptWarn();
#endif

// ALWAYS AVAILABLE
extern unsigned int hasErrors;

void AddWarning(char* buffer);
void AddError(char* buffer);
char* ReadNextSystemToken(FILE* in,char* ptr, char* word, bool separateUnderscore=true,bool peek=false);
char* ReadSystemToken(char* ptr, char* word, bool separateUnderscore=true);

#define BADSCRIPT(...) {ScriptError(); Log((compiling) ? BADSCRIPTLOG : STDUSERLOG , __VA_ARGS__); JumpBack();}
#define WARNSCRIPT(...) {ScriptWarn(); Log(STDUSERLOG, __VA_ARGS__); }

#endif
