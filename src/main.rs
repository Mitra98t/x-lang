mod expressions;
/**
* Start of the cretion of a language aimed to be used for learning purposes.
*/
mod lexer;
mod parser;

fn main() {
    let inputs = vec![["
class Person < Object {
    let age = 3;

    fn new(age) {
        age = age;
    }
    fn get_age() {
        print age;
    }
}

let p = Person.new(15);
p.get_age();
"]];

    for input_str in inputs.iter().flatten() {
        let input = input_str.to_string();
        let mut l = lexer::Lexer::new(input.clone());

        println!("{input}");
        let tok_list: Vec<lexer::Token> = l.run();
        // println!("Tokens:");
        // tok_list.clone().into_iter().for_each(|tok| {
        //     println!("{:?}", tok);
        // });

        let mut p = parser::Parser::new(tok_list);
        let nodes = p.parse();
        println!("Nodes:");
        match nodes {
            Ok(nodes) => {
                parser::Parser::pretty_print_ast(nodes);
            }
            Err(e) => {
                println!("{:?}", e);
            }
        }
        println!("-------------------");
    }
}
