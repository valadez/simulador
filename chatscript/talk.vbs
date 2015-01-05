' script courtesy of Don Patrick 

Set voice = CreateObject("sapi.spvoice")
if(WScript.Arguments.Count = 1) then
 Dim text
 text = WScript.Arguments(0)
 voice.Speak " "
else 
 voice.Speak " "
end if  