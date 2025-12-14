/*
 * Copyright 2012-2025 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.springframework.samples.petclinic.model;

import jakarta.persistence.Column;
import jakarta.persistence.MappedSuperclass;
import jakarta.validation.constraints.NotBlank;

/**
 * Simple JavaBean domain object representing a person.
 *
 * @author Ken Krebs
 */
@MappedSuperclass
public class Person extends BaseEntity {

	@Column(name = "first_name")
	@NotBlank
	private String firstName;

	@Column(name = "last_name")
	@NotBlank
	private String lastName;

	/*
	 * @ requires true; // no precondition ensures \result != null &&
	 * \result.equals(firstName); assignable \nothing;
	 *
	 * @
	 */
	public String getFirstName() {
		return this.firstName;
	}

	/*
	 * @ requires firstName != null && !firstName.isEmpty(); ensures
	 * this.firstName.equals(firstName); assignable this.firstName;
	 *
	 * @
	 */
	public void setFirstName(String firstName) {
		this.firstName = firstName;
	}

	/*
	 * @ requires true; // no precondition ensures \result != null &&
	 * \result.equals(lastName); assignable \nothing;
	 *
	 * @
	 */
	public String getLastName() {
		return this.lastName;
	}

	/*
	 * @ requires lastName != null && !lastName.isEmpty(); ensures
	 * this.lastName.equals(lastName); assignable this.lastName;
	 *
	 * @
	 */
	public void setLastName(String lastName) {
		this.lastName = lastName;
	}

}
