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
 * @version 1.0.0
 * @since 1.0.0
 * 
 */
public class StackElement {

	private OCLExpression<EClassifier> exp;
	public StackExp sourceStack;

	public void setExp(OCLExpression<EClassifier> c) {
		exp = c;
	}

	public OCLExpression<EClassifier> getExp() {
		return exp;
	}

	public void push(OCLExpression<EClassifier> c, boolean toSon) {
		sourceStack.push(c, toSon);
	}

	public StackElement(StackExp father, IRI ontoIRI, String pkg) {
		sourceStack = new StackExp(father, ontoIRI, pkg);
	}

	public void endStack() {
		sourceStack.endStack();
	}

	public OCLExpression<EClassifier> getExpression() {
		return exp;
	}
}
