#r "Microsoft.Build.dll"
#r "Microsoft.Build.Framework.dll"
#load "Library.fs"

open UnitTestMarker

let questions =
    [
        "Polarity", 5
        "InRange", 7
        "Sum", 8
        "FireSale", 10
        "IndexOfGEQ", 10
        "DivvyUp", 12
        "Splitter", 13
        "OnlyYou", 16
        "GotWords", 18
        "BigSmall", 18
        "RotL", 20
        "SpecialNumber", 30
        "Decode", 46
    ]

//Submissions.init @"C:\Users\Me\Desktop\PartB\PracExamJune2017\bin\Debug\PracExamJune2017.exe" @"c:\temp\CSc101 Practical Exam, June 2017" [".+\.sln$"] [".*ORIGINAL.*"] (Map.ofList questions)