use std::string::String;


pub enum LambdaTerm {
    Variable(String),
    App(Box<LambdaTerm>, Box<LambdaTerm>),
    Lambda(Vec<String>, Box<LambdaTerm>)
}
