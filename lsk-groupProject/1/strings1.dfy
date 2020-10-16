method isPrefix(pre: string, str: string) returns (res:bool)
 requires |pre|>=0
 requires |str|>=0
 requires |str|>=|pre|
 ensures res == true || res == false
{   
    if (|pre| == 0){
     return true;
    }else{
        if (str[..|pre|]==pre)
        { return true; }
    else
        { return false; }
    }
}

method isSubstring(pre: string, str: string) returns(res: bool)
    requires |pre| >= 0
    requires |str| >= 0
    requires |str| >= |pre|
    ensures res == true || res == false
{
    var strLeng :int := |str|;
    var preLeng :int := |pre|;
    var i :int := 0; 

    var boolean:bool;

    while i < strLeng-preLeng
    decreases strLeng-preLeng-i
    invariant  0 <= i <= strLeng
    {
        boolean := isPrefix(pre,str[i..]);
        if boolean {
            return  true;
        }

        i:=i+1;
    }
    return false;
}


method haveCommonKSubstring(k: nat, str1: string, str2: string) returns (found: bool)
    requires k >= 0
    requires |str1| >= 0
    requires |str2| >= 0
    requires |str1| >= k && |str2| >=k
    ensures found == true || found == false
{
    found := false;

    var str1Leng :nat := |str1|;
    var str2Leng :nat := |str2|;

    var lowerbound :nat:= 0;
    var upperbound :nat:=str1Leng-k;

    var tmpSubstring :string;
    var ifFound :bool;
    while lowerbound <= upperbound
    decreases upperbound-lowerbound
    invariant 0 <= lowerbound
    {   
        tmpSubstring := str1[lowerbound..(lowerbound+k)];
        ifFound := isSubstring(tmpSubstring,str2);
        if (ifFound == true){
            found := true;
            return found;
        }
        lowerbound := lowerbound+1; 
    }
    return found;
}

method maxCommonSubstringLength(str1: string, str2: string) returns (len:nat)
    requires |str1| > 0
    requires |str2| > 0
    ensures 0 <= len
{
    var str1Leng :nat := |str1|;
    var str2Leng :nat := |str2|;
    
    var smallerString : string;
    var largerString : string;

    if (str1Leng < str2Leng){
        smallerString := str1;
        largerString := str2;
    } else{
        smallerString := str2;
        largerString := str1;
    }

    var smallerStringLeng := |smallerString|;

    var offset :nat := 0;
    var ifFound : bool := false;

    while smallerStringLeng >= offset
    decreases smallerStringLeng-offset
    invariant 0 <= offset
    {   
        len := smallerStringLeng-offset;
        ifFound:= haveCommonKSubstring(len,smallerString,largerString);
        if (ifFound == true){
            return len;
        }
        offset := offset+1;
    }
    return len;
}