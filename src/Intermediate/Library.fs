module Intermediate.Intermediate

type MonoMode =
    | MSize of int
    | MType of Intermediate.Type.Type

type Location =
    | Static
    | Unambiguous
    | Automatic
    | Irregular
