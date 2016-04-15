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
import org.eclipse.ocl.expressions.OCLExpression;
import org.semanticweb.owlapi.model.IRI;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.1.0
 * @since 1.0.0
 * 
 */
public class StackElement {

	//OCLExpression stored in this StackElement
	private OCLExpression<EClassifier> exp;
	//This StackElement inner stack
	public StackExp innerStack;

	public void setExp(OCLExpression<EClassifier> expression) {
		exp = expression;
	}


	/**
	 * Inserts the provided Expression into the this StackElement inner stack
	 * @param expression
	 * 		The expression to be inserted
	 * @param toInnerStack
	 * 		Indicates if the expression should be inserted directly in the "sourceStack" inner stack
	 * 		or in the inner stack of its top element.
	 */
	public void push(OCLExpression<EClassifier> expression, boolean toInnerStack) {
		innerStack.push(expression, toInnerStack);
	}

	/**
	 * 
	 * @param father
	 * 		A pointer to the StackExp containing this StackElement if any.
	 * @param ontoIRI
	 * 		The ontology IRI for building concepts
	 * @param pkg
	 * 		The package name where the OCL constraint is contained
	 */
	public StackElement(StackExp father, IRI ontoIRI, String pkg) {
		innerStack = new StackExp(father, ontoIRI, pkg);
	}

	/**
	 * Fires the event at the top element at the inner stack recursively untils reach a stack
	 * where the "pushToSon" variable is set to false. Then, sets the fatherStack "pushToSon" variable to false.
	 */
	public void endStack() {
		innerStack.endStack();
	}

	
	/**
	 * Returns the OCL Expression stored at this StackElement
	 * @return
	 * 		The OCL Expression stored at this StackElement
	 */
	public OCLExpression<EClassifier> getExpression() {
		return exp;
	}
}
