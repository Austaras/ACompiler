module Regex.Tests

open NUnit.Framework
open Regex

[<Test>]
let Concat () =
    let reg = Regex("123")
    Assert.True(reg.match_str "123")
    Assert.False(reg.match_str "234")
    Assert.False(reg.match_str "1234")

[<Test>]
let Or () =
    let reg = Regex("aac|abc")
    Assert.True(reg.match_str "aac")
    Assert.True(reg.match_str "abc")
    Assert.False(reg.match_str "acc")

    let reg = Regex("|c")
    Assert.True(reg.match_str "c")
    Assert.False(reg.match_str "ab")

[<Test>]
let Many () =
    let reg = Regex("a*a")
    Assert.True(reg.match_str "aaa")
    Assert.False(reg.match_str "aaab")

    let reg = Regex("a+")
    Assert.True(reg.match_str "aa")
    Assert.False(reg.match_str "")

    let reg = Regex("a*b*")
    Assert.True(reg.match_str "aabb")
    Assert.False(reg.match_str "abab")

[<Test>]
let Complex () =
    let reg = Regex("a|ab*")
    Assert.True(reg.match_str "abbb")
    Assert.False(reg.match_str "aa")

    let reg = Regex("a(b|c)*")
    Assert.True(reg.match_str "abcbbc")
    Assert.False(reg.match_str "aa")

    // even number of a
    let reg = Regex("((b|c)*a(b|c)*a)*(b|c)*")
    Assert.True(reg.match_str "abcbbcabcc")
    Assert.False(reg.match_str "abaca")
