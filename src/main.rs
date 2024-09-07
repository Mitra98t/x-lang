mod expressions;
/**
* Start of the cretion of a language aimed to be used for learning purposes.
*/
mod lexer;
mod parser;

fn main() {
    let inputs = vec![["
fn succ(x ) {
    return x + 1;
}

while (x < 10) {
    x = succ(x);
}

print(x);
"]];

    for input_str in inputs.iter().flatten() {
        let input = input_str.to_string();
        let mut l = lexer::Lexer::new(input.clone());

        println!("{input}");
        let tok_list: Vec<lexer::Token> = l.run();
        println!("Tokens:");
        tok_list.clone().into_iter().for_each(|tok| {
            println!("{:?}", tok);
        });

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
