module Regex.Tests

open Xunit
open Regex

[<Fact>]
let Concat () =
    let reg = Regex("123")
    Assert.True(reg.MatchStr "123")
    Assert.False(reg.MatchStr "234")
    Assert.False(reg.MatchStr "1234")

[<Fact>]
let Or () =
    let reg = Regex("aac|abc")
    Assert.True(reg.MatchStr "aac")
    Assert.True(reg.MatchStr "abc")
    Assert.False(reg.MatchStr "acc")

    let reg = Regex("|c")
    Assert.True(reg.MatchStr "c")
    Assert.False(reg.MatchStr "ab")

[<Fact>]
let Many () =
    let reg = Regex("a*a")
    Assert.True(reg.MatchStr "aaa")
    Assert.False(reg.MatchStr "aaab")

    let reg = Regex("a+")
    Assert.True(reg.MatchStr "aa")
    Assert.False(reg.MatchStr "")

    let reg = Regex("a*b*")
    Assert.True(reg.MatchStr "aabb")
    Assert.False(reg.MatchStr "abab")

[<Fact>]
let Complex () =
    let reg = Regex("a|ab*")
    Assert.True(reg.MatchStr "abbb")
    Assert.False(reg.MatchStr "aa")

    let reg = Regex("a(b|c)*")
    Assert.True(reg.MatchStr "abcbbc")
    Assert.False(reg.MatchStr "aa")

    // even number of a
    let reg = Regex("((b|c)*a(b|c)*a)*(b|c)*")
    Assert.True(reg.MatchStr "abcbbcabcc")
    Assert.False(reg.MatchStr "abaca")
