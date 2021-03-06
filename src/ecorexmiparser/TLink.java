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

package ecorexmiparser;

/**
 * @author Cassio Santos, Christiano Braga
 * @version 1.0.0
 * @since 1.0.0
 * 
 */
public class TLink {

	private String type;
	private Integer position;

	public TLink(String type, Integer position) {
		this.type = type;
		this.position = position;
	}

	public String getType() {
		return type;
	}

	public Integer getPosition() {
		return position;
	}

}
