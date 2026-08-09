pub type Env = Vec<Defn>;

type Label = String;
type TpName = String;
type VarName = String;
type ProcName = String;
type Parm = (VarName, Type);

#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Type {
    TpName(TpName),
    One,
    Times(Box<Type>, Box<Type>),
    Plus(Vec<(Label, Type)>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Pattern {
    InjPat(Label, VarName),
    PairPat(VarName, VarName),
    UnitPat,
}

#[derive(Debug, PartialEq, Eq)]
pub enum Cmd {
    Read(VarName, Vec<(Pattern, Cmd)>),
    Write(VarName, Pattern),
    Cut(VarName, Type, Box<Cmd>, Box<Cmd>),
    Id(VarName, VarName),
    Call(ProcName, VarName, Vec<VarName>),
}

#[derive(Debug, PartialEq, Eq)]
pub enum Defn {
    TypeDefn(TpName, Type),
    ProcDefn(ProcName, Parm, Vec<Parm>, Cmd),
    FailDefn(Box<Defn>),
}
