/**
 *   This file is part of ECore Consistency Checker (ECC).
 *
 *   ECC is a free software: you can redistribute it and/or modify
 *   it under the terms of the GNU General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   ECC is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU General Public License for more details.
 *
 *   You should have received a copy of the GNU General Public License
 *   along with ECC.  If not, see <http://www.gnu.org/licenses/>.
 * 
 */

package consistencychecker;

import org.eclipse.emf.ecore.EClassifier;
import org.eclipse.emf.ecore.EOperation;
import org.eclipse.emf.ecore.EReference;
import org.eclipse.ocl.expressions.IteratorExp;
import org.eclipse.ocl.expressions.OCLExpression;
import org.eclipse.ocl.expressions.OperationCallExp;
import org.eclipse.ocl.expressions.PropertyCallExp;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.IRI;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassExpression;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLObjectProperty;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.1.0
 * @since 1.0.0
 * 
 */
public class StackExp {

	protected static final String SPACE = " ";
	protected static final String DOT = ".";
	protected static final String OCL_AS_TYPE = "oclAsType";
	protected static final String IS_EMPTY = "isEmpty";
	protected static final String SELECT = "select";
	protected static final String DOUBLE_COLON = "::";
	protected static final String BLANK = "";
	protected static final String ARROW = "->";
	protected static final String NOT_EMPTY = "notEmpty";
	protected static final String IMPLIES = "implies";
	protected static final String OR = "or";
	protected static final String AND = "and";
	protected static final String NOT = "not";
	protected static final String OCL_IS_TYPE_OF = "oclIsTypeOf";
	protected static final String PARENTHESIS = "()";
	protected static final String PARENTHESIS_FOR_FORMAT = "(%s)";
	protected static final String POUND_SIGN = "#";
	protected static final String CLASS_POSFIX = "class";
	protected static final String ROLE_POSFIX = "role";
	protected String PACKAGE_PREFIX;
	protected IRI ontologyIRI_;
	protected OWLDataFactory owlDataFactory_;
	protected OWLClassExpression topExp;
	protected boolean pushToSon;
	protected int stackPoint;
	protected StackElement[] stack;
	public StackExp fatherStack;
	protected String CLASS_NAME_BUILDER = "";

	/**
	 * @param fatherStack
	 * 		The main stack to which this one is associated, if any.
	 * @param ontoIRI
	 * 		The ontology IRI used when generating OWL Concepts
	 * @param pkg
	 * 		The name of the package where the OCL Expression are declared
	 */
	public StackExp(StackExp fatherStack, IRI ontoIRI, String pkg) {
		pushToSon = false;
		stackPoint = 0;
		this.fatherStack = fatherStack;
		owlDataFactory_ = OWLManager.createOWLOntologyManager().getOWLDataFactory();
		ontologyIRI_ = ontoIRI;
		PACKAGE_PREFIX = pkg;
		topExp = null;
		CLASS_NAME_BUILDER = ontologyIRI_ + POUND_SIGN + PACKAGE_PREFIX + "(" + "%s" + "[" + CLASS_POSFIX + "]" + ")";
	}

	/**
	 * Inserts an expression into the stack and returns the stack where the next elements must be inserted
	 * @param expression
	 * 		The OCLExpression being stacked
	 * @param toInnerStack
	 * 		When false the next elements should be inserted in the current stack. 
	 * 		Else, the next elements must be inserted in the inner stack of the StackElement 
	 * 		containing the recently added expression.
	 * @return
	 * 		The StackExp where the next expression must be inserted
	 */
	public StackExp push(OCLExpression<EClassifier> expression, boolean toInnerStack) {
		//Declares the return variable
		StackExp result = this;
		//If the stack is empty, instantiates it with 100 positions
		if (stack == null) {
			stack = new StackElement[100];
		}
		//Inserts into the stack at the first free position a new StackElement
		stack[stackPoint] = new StackElement(this, ontologyIRI_, PACKAGE_PREFIX);
		//Stores the provided expression in the new StackElement
		stack[stackPoint].setExp(expression);
		if (toInnerStack) {
			//If "toInnerStack" is true, then set the return variable with a pointer to the inner stack created
			result = stack[stackPoint].innerStack;
		}
		//Increases the stackPoint variable, pointing it to the next free position
		stackPoint++;
		//Doubles the array size if reached its limit
		if(stackPoint == stack.length){
			StackElement[] temp = new StackElement[stack.length*2];
			System.arraycopy(stack, 0, temp, 0, stack.length);
			stack = temp;
		}
		return result;
	}

	/**
	 * Inserts an OCLExpression in the inner stack of the top StackExp
	 * @param expression
	 * 		The expression to be inserted
	 * @param toInnerStack
	 * 		When false the next elements should be inserted in the inner stack. 
	 * 		Else, the next elements must be inserted in the inner stack of the StackElement 
	 * 		containing the recently added expression.
	 * @return
	 */
	public StackExp pushToSon(OCLExpression<EClassifier> expression, boolean toInnerStack) {
		//Inserts the provided expression in the inner stack of the top StackExp
		return stack[stackPoint - 1].innerStack.push(expression, toInnerStack);
	}

	/**
	 * Changes the expression at the top of the stack to a "select" Expression
	 */
	public void changeUpElementToSelect() {
		stack[stackPoint - 1].getExpression().setName(SELECT);
	}

	/**
	 * Fires the event at the top element at the inner stack recursively untils reach a stack
	 * where the "pushToSon" variable is set to false. Then, sets the fatherStack "pushToSon" variable to false.
	 */
	public void endStack() {
		if (pushToSon) {
			stack[stackPoint - 1].endStack();
		} else {
			fatherStack.pushToSon = false;
		}
	}

	/**
	 * Returns the element at the top of the stack, and empty that position
	 * 
	 * @return
	 * 		Element at the top of the stack
	 */
	public StackElement pop() {
		//Decreases the value of the variable pointing to the next available position
		stackPoint--;
		//Returns the element at the top of the stack
		return stack[stackPoint];
	}

	/**
	 * Returns the expression contained at the top StackElement
	 * @return
	 * 		The expression contained at the top StackElement
	 */
	public OCLExpression<EClassifier> getTopElementExpression() {
		//Points to the last occupied position
		int lastOccupiedPosition = stackPoint - 1;
		//Returns the element at this position
		return stack[lastOccupiedPosition].getExpression();
	}

	/**
	 * Transforms the OCL Expression stored in the multi-level stack into an OWLClassExpression (DL Concept)
	 * @return
	 * 		The OWLClasExpressin representing the normalized OCL Expression
	 */
	public OWLClassExpression resolveStack() {
		//Declare the return variable
		OWLClassExpression result = null;
		//Extracts the Top StackElement, and releases that position
		StackElement s = pop();
		//Extracts the OCLExpression associated to it
		OCLExpression<EClassifier> exp = s.getExpression();
		//Checks if the Expression in OCL operation
		if (exp instanceof OperationCallExp) {
			//Performs the appropriated cast
			OperationCallExp<EClassifier, EOperation> resExp = (OperationCallExp<EClassifier, EOperation>) exp;
			//Check the type of operation being handled
			switch(resExp.getReferredOperation().getName()){
			case OCL_IS_TYPE_OF:
				//Extracts the type to which oclIsTypeOf() is beign applied
				String argumentNameTypeOf = resExp.getArgument().get(0).toString()
				.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString().split(DOUBLE_COLON).length - 1];
				//Return an OWLClass representing the type being checked
				result = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, argumentNameTypeOf)));
				break;
			case NOT:
				//Returns a concept representing the complement of the resulting concept of the remaining stack
				result = owlDataFactory_.getOWLObjectComplementOf(this.resolveStack());
				break;
			case AND:
				//Solves the sourcestack variable in order to obtain the concept 
				//representing the first term of the "and" operator
				OWLClassExpression rightSideAnd = s.innerStack.resolveStack();
				//Returns an union between the concept representing the first term of the "and" operator
				//and the remaining stack, representing the second term of the "and" operator
				result = owlDataFactory_.getOWLObjectIntersectionOf(this.resolveStack(), rightSideAnd);
				break;
			case OR:
				//Solves the sourcestack variable in order to obtain the concept 
				//representing the first term of the "or" operator
				OWLClassExpression rightSideOr = s.innerStack.resolveStack();
				//Returns an union between the concept representing the first term of the "or" operator
				//and the remaining stack, representing the second term of the "or" operator
				result = owlDataFactory_.getOWLObjectUnionOf(this.resolveStack(), rightSideOr);
				break;
			case IMPLIES:
				//Solves the sourcestack variable in order to obtain the concept 
				//representing the second term of the "implies" operator
				OWLClassExpression rightSideImplies = s.innerStack.resolveStack();
				//Solves the remaining stack in order to to obtain the concept 
				//representing the first term of the "implies" operator.
				//In order to properly represent the implication, this concept must be
				//used in a complement.
				OWLClassExpression sourceComplement = owlDataFactory_.getOWLObjectComplementOf(this.resolveStack());
				//Returns an union between the complement of the first term and the second term
				result = owlDataFactory_.getOWLObjectUnionOf(sourceComplement, rightSideImplies);
				break;
			case NOT_EMPTY:
				//If the operation is an "notEmpty()" then, its OWL representation 
				//is the representation of the expression to which this operator is being applied
				result = this.resolveStack();
				break;
			case IS_EMPTY:
				//If the operation is an "isEmpty()" then, its OWL representation 
				//is the complement representation of the expression to which this operator is being applied
				result = owlDataFactory_.getOWLObjectComplementOf(this.resolveStack());
				break;
			case OCL_AS_TYPE:
				//Extracts the type to which oclIsTypeOf() is beign applied
				String argumentNameAsType = resExp.getArgument().get(0).toString()
				.split(DOUBLE_COLON)[resExp.getArgument().get(0).toString().split(DOUBLE_COLON).length - 1];
				//Creates an OWLClass representing the type being casted
				OWLClass arg = owlDataFactory_.getOWLClass(IRI.create(String.format(CLASS_NAME_BUILDER, argumentNameAsType)));
				//Replaces the concept stored in the "topExp" variable
				//with an intersection between the the created OWLClass and the concept
				//stored in the "topExp" variable. 
				topExp = owlDataFactory_.getOWLObjectIntersectionOf(arg, topExp);
				result = this.resolveStack();
				break;
			default:
				break;
			
			}
		} else {
			//Checks if the Expression is an OCL property call
			if (exp instanceof PropertyCallExp) {
				//Performs the appropriated cast
				PropertyCallExp<EClassifier, EReference> resExp = (PropertyCallExp<EClassifier, EReference>) exp;
				//Creates the OWL property representing the OCL Property
				OWLObjectProperty roleLeft = owlDataFactory_.getOWLObjectProperty(IRI.create(ontologyIRI_ + POUND_SIGN
						+ PACKAGE_PREFIX + resExp.getReferredProperty().getEOpposite().getEType().getName()
						+ resExp.getReferredProperty().getName() + resExp.getReferredProperty().getEType().getName()
						+ ROLE_POSFIX));
				if (topExp == null) {
					//If topExp variable is null, then creates a Concept representing that
					//Exists such property leading to Top
					topExp = owlDataFactory_.getOWLObjectSomeValuesFrom(roleLeft, owlDataFactory_.getOWLThing());
				} else {
					//If topExp variable is null, then creates a Concept representing that
					//Exists such property leading to the concept stored in "topExp"
					topExp = owlDataFactory_.getOWLObjectSomeValuesFrom(roleLeft, topExp);
				}
				if (stackPoint == 0) {
					//If the the recursion has reached the last element, then the "topExp"
					//concept is the result
					result = topExp;
				} else {
					//If the the recursion hasn't reached the last element, then the result
					//is the concept representing the remaining stack;
					result = this.resolveStack();
				}
			} else {
				//Checks if the Expression is a OCL iterator
				if (exp instanceof IteratorExp) {
					//If the expression is an Iterator, the "topExp" receives the Concept
					//representing the source stack
					topExp = s.innerStack.resolveStack();
					//Returns the concept representing the remaining stack
					result = this.resolveStack();
				}
			}
		}
		return result;
	}

	/**
	 * Converts the OCL stored in the multi-level stack in this variable to an OCL Expression String
	 * 
	 * @return
	 * 		The OCL expression form of the expression stored at this stack
	 */
	public String print() {
		int originalStackPoint = stackPoint;
		//Instantiates the variable that will contain the String with the resulting expression with a blank String
		String ans = BLANK;
		//Removes the element at the top of the stack and stores it in the "currentElement" variable
		StackElement currentElement = pop();
		//Extracts the expression from the "currentElement"
		OCLExpression<EClassifier> elem = currentElement.getExpression();
		//Checks if the expression is an OCL Operation
		if (elem instanceof OperationCallExp<?, ?>) {
			//Casts the OCLExpression variable to an OperationCallExp variable  
			OperationCallExp<EClassifier, EOperation> operationExp = (OperationCallExp<EClassifier, EOperation>) elem;
			//Checks the type of the operation being printed and adds the text representing it to the "ans" 
			//If the operation is an "not","and","or" or "implies", an recursive call to this method occurs
			switch(operationExp.getReferredOperation().getName()){
				case OCL_IS_TYPE_OF:
					//Extracts the name of the Type being checked
					String argumentName = operationExp.getArgument().get(0).toString()
							.split(DOUBLE_COLON)[operationExp.getArgument().get(0).toString().split(DOUBLE_COLON).length - 1];
					ans = OCL_IS_TYPE_OF + String.format(PARENTHESIS_FOR_FORMAT, argumentName);
					break;
				case NOT:
					ans = NOT + String.format(PARENTHESIS_FOR_FORMAT, print());
					break;
				case AND:
					ans = print() + SPACE + AND + SPACE + currentElement.innerStack.print();
					break;
				case OR:
					ans = print() + SPACE + OR + SPACE + currentElement.innerStack.print();
					break;
				case IMPLIES:
					ans = print() + SPACE + IMPLIES + SPACE + currentElement.innerStack.print();
					break;
				case NOT_EMPTY:
					ans = print() + ARROW + NOT_EMPTY + PARENTHESIS;
					break;
				case IS_EMPTY:
					ans = print() + ARROW + IS_EMPTY + PARENTHESIS;
					break;
				case OCL_AS_TYPE:
					//Extracts the name of the Type being casted
					String argumentNameAsType = operationExp.getArgument().get(0).toString()
					.split(DOUBLE_COLON)[operationExp.getArgument().get(0).toString()
							.split(DOUBLE_COLON).length - 1];
					ans = OCL_IS_TYPE_OF + String.format(PARENTHESIS_FOR_FORMAT, argumentNameAsType);
					break;
				default:
					break;
			}
		} else {
			//Checks if the expression is an OCL Property
			if (elem instanceof PropertyCallExp) {
				//Casts the OCLExpression variable to an PropertyCallExp variable  
				PropertyCallExp<EClassifier, EReference> resExp = (PropertyCallExp<EClassifier, EReference>) elem;
				//Extracts the role to which this property refers to
				String role = resExp.getReferredProperty().getName();
				//If stackPoint is zero, then the role name is the first element of the expression
				if (stackPoint == 0) {
					ans = role;
				} else {
					//If stackPoint is not zero, then the role name in the middle of the expression and should be preceded by a dot.
					ans = DOT + role;
				}
			} else {
				//Checks if the expression is an OCL Iterator
				if (elem instanceof IteratorExp) {
					//If stackPoint is not zero, then the operator in the middle of the expression is an implies sign
					if (stackPoint != 0) {
						ans = ARROW;
					}
					//If stackPoint is zero, then recursive calls to this method are applied and concatenated to form the OCL Expression String
					ans = print() + ans + elem.getName() + String.format(PARENTHESIS_FOR_FORMAT, currentElement.innerStack.print());
				}
			}
		}
		stackPoint = originalStackPoint;
		return ans;
	}
}
