structure tigertips =
struct


datatype Permission = RO | RW


type unique = unit ref
datatype Tipo = TUnit
	| TNil
	| TInt of Permission
	| TString
	| TArray of Tipo ref  * unique
	| TRecord of (string * Tipo ref * int) list * unique
	| TTipo of string 

end
