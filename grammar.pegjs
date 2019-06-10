{

var latexmappings = 
{"FORALL": " \\forall ",
"EXISTS": " \\exists ",
"AND":" \\land ",
"OR":" \\lor ",
"IMPLIES":" \\rightarrow ",
"NOT":" \\lnot "};

function Relation(x){
  this.name = x.split("(")[0];
    this.vars = x.split("(")[1].split(")")[0].split(",");
    
    this.latex = function() {
      return this.name + "(" +this.vars.join(",")+ ")";
  }
    
    this.arraylatex = function(line,depth,maxdepth) {
    return line + "&".repeat(depth) + this.latex() + "\\\\";
  }
}

function Binop(name, left, right){
  this.op = name;
    this.left = left;
    this.right = right;
    
    this.latex = function() {
        var left = this.left.latex();
        console.log("HELLO", left, this.left);
        if(this.left.op != undefined){
        console.log("GET PAREN HELLO");
            left = " ( " + left + " ) ";
        }

        var right = this.right.latex();
        if(this.right.op != undefined){
            right = " ( " + right + " ) ";
        }

       return left + latexmappings[this.op] + right;
    }

    this.arraylatex = function(line,depth,maxdepth) {
        return line + "&".repeat(depth) + this.latex() + "\\\\";
    }   
}


    
function Unop(name, left){
  this.op = name;
    this.left = left;
    
    this.latex = function() {
        left = this.left.latex();
        if(! this.left instanceof Relation){
            left = " ( " + left + " ) ";
        }
       return latexmappings[this.op]+" "+left;  
    }

    this.arraylatex = function(line,depth,maxdepth) {
        return line + "&".repeat(depth) + this.latex() + "\\\\";
    }
    
}



function Quantifier(name, bound, formula){
  this.op = name
    this.bound = bound
    this.formula = formula
    
    this.latex = function() {
       return latexmappings[this.op]+" "+this.bound+" "+"("+this.formula.latex()+")"; 
    }

    this.arraylatex = function(line,depth,maxdepth) {
        return line + "&".repeat(depth) + this.latex() + "\\\\";
    }
}


function Rule(name, args, range){
  this.name = name
    this.args = args
    this.range= range
    
    this.latex = function() {
        var tail;
        if(this.range){
            tail = this.args.join("-");
        } else {
            tail = this.args.join(" ")
        }

       return "\\text{" + this.name+" "+tail+"}"; 
    } 
}

function Contradiction(){
  this.op = "BOT";
  this.latex = function() {
      return " \\bot ";
    }
}

function Justification(formula, rule){
  this.formula = formula
    this.rule = rule
    
    this.arraylatex = function(line,depth,maxdepth) {
        return line + "&".repeat(depth) + this.formula.latex()
        +"&".repeat(maxdepth-depth) +this.rule.latex() + "\\\\";
    }
}

function Proof(premises, conclusions){
  this.premises = premises;
    this.conclusions = conclusions;
    
    this.arraylatex = function(line,depth,maxdepth) {
        depth++;
        //var out = "\begin{array}{c|ll}\n"

        var out = "";

        for(var i = 0; i < this.premises.length; i++){
            out += this.premises[i].arraylatex(line++,depth,maxdepth);
        }
    out += "\\hline\n"
        for(var i = 0; i < this.conclusions.length; i++){
            var res = this.conclusions[i].arraylatex(line++,depth,maxdepth);
            if (Array.isArray(res)){
                line = res[0];
                out += res[1];
            } else {
                out +=res;
            }
        }

        return [line, out];
        //out += "\end{array}\n"

    }

    this.depth = function(depth) {
        depth++;
        var maxdepth = depth;

        for(var i = 0; i < this.conclusions.length; i++){
            if(this.conclusions[i] instanceof Proof){
                var ld = this.conclusions[i].depth(depth);
                if(ld > maxdepth){
                    maxdepth = ld;
                }
            }
        }

        return maxdepth;
    }
    
}



    
}

//((R(x) & R(u)) -> ~R(x)) | ~R(c)
//(@y@x R(x,x)) -> (@x R(x,x))

/*
Premises
{
  A->B
  A->C
}
Conclusion
{
  Premises
  {
  A
  }
  Conclusion
  {
  B   < E ...
    C   < E  ...
    B&C < I -1,-2
  }
  
  A -> (B&C) > I 3-6
}


*/

start = Proof 




Proof "proof" =
_"Premises" _ "{" _
  plist:( _ Formula )+

_ "}" _ "Conclusions" _ "{" _
  clist:(_ Subproof )*
_ "}" _ 

{ 
  var premises = [];
    for(var i = 0; i < plist.length; i++){
      premises.push(plist[i][1]);
    }
  
  var conclusions = [];
    for(var i = 0; i < clist.length; i++){
      conclusions.push(clist[i][1]);
    }
    
    return new Proof(premises,conclusions);
}


Subproof "subproof" 
  = _ x:(Formula) _ "<" _ y:Rule {return new Justification(x,y)}
  / _ x:("#") _ "<" _ y:Rule {return new Justification(new Contradiction(),y)}
  / x:Proof {return x}


Rule "rule" 
  = _ x:("I" / "E") _ y:Integer _ "\-" _ z:Integer  _ 
  {
    return new Rule(x, [y,z], true)
  }
  
  /_ x:("I" / "E" / "X") lines:(_ Integer)+  _ 
  {
    var args = [];
    for(var i = 0; i < lines.length; i++){
      args.push(lines[i][1]);
    }
    
    return new Rule(x, args, false)
  }
  
  
Formula "formula"
  = _ x:Expression _ {return x}
  / _ "forall" _ x:Element _ y:Formula _ {return new Quantifier("FORALL", x, y)}
  / _ "@" _ x:Element _ y:Formula _ {return new Quantifier("FORALL", x, y)}
  / _ "E" _ x:Element _ y:Formula _ {return new Quantifier("EXISTS", x, y)}
  / _ "#" _ x:Element _ y:Formula _ {return new Quantifier("EXISTS", x, y)}
  / _ "exists" _ x:Element _ y:Formula _ {return new Quantifier("EXISTS", x, y)}
  / _ "(" _ x:Expression _ "&" _ y:Expression _ ")" _ { return new Binop("AND",x,y) }
  / _ "(" _ x:Expression _ "|" _ y:Expression _ ")" _ { return new Binop("OR",x,y) }
  / _ "(" _ x:Expression _ "->" _ y:Expression _ ")" _  { return new Binop("IMPLIES",x,y) }
  
Expression "expression"
  = _ "~" _ x:Statement _ { return new Unop("NOT",x) }
  / _ x:Statement _ "&" _ y:Statement _ { return new Binop("AND",x,y) }
  / _ x:Statement _ "|" _ y:Statement _ { return new Binop("OR",x,y) }
  / _ x:Statement _ "->" _ y:Statement _  { return new Binop("IMPLIES",x,y) }
  / _ x:Statement _ {return x}
  
Statement "statement"
  = _ "(" _ x:Statement _ ")" _ {return x}
  / _ "(" _ x:Formula _ ")" _ {return x}
  / _ "~" _ x:Relation _ { return new Unop("NOT",x) }
  / _ x:Relation _ {return x}

Relation "relation"
  = name:[A-Z]+"("  [a-z]+ ( ","  [a-z]+)*  ")" { return new Relation(text()); }

Element "element"
  = _ [a-z]+ { return text() }

Integer "integer"
  = _ [0-9]+ _ { return parseInt(text(), 10); }

_ "whitespace"
  = [ \t\n\r]*

              