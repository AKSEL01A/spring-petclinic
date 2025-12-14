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
package org.springframework.samples.petclinic.owner;

import java.time.LocalDate;
import java.util.Collection;
import java.util.LinkedHashSet;
import java.util.Set;

import org.springframework.format.annotation.DateTimeFormat;
import org.springframework.samples.petclinic.model.NamedEntity;

import jakarta.persistence.CascadeType;
import jakarta.persistence.Column;
import jakarta.persistence.Entity;
import jakarta.persistence.FetchType;
import jakarta.persistence.JoinColumn;
import jakarta.persistence.ManyToOne;
import jakarta.persistence.OneToMany;
import jakarta.persistence.OrderBy;
import jakarta.persistence.Table;

/**
 * Simple business object representing a pet.
 *
 * @author Ken Krebs
 */
@Entity
@Table(name = "pets")
public class Pet extends NamedEntity {

	@Column(name = "birth_date")
	@DateTimeFormat(pattern = "yyyy-MM-dd")
	private LocalDate birthDate;

	@ManyToOne
	@JoinColumn(name = "type_id")
	private PetType type;

	@OneToMany(cascade = CascadeType.ALL, fetch = FetchType.EAGER)
	@JoinColumn(name = "pet_id")
	@OrderBy("date ASC")
	private final Set<Visit> visits = new LinkedHashSet<>();

	/*
	 * @ requires birthDate != null; ensures \result == birthDate; assignable
	 * this.birthDate;
	 *
	 * @
	 */
	public void setBirthDate(LocalDate birthDate) {
		this.birthDate = birthDate;
	}

	/*
	 * @ ensures \result == birthDate; assignable \nothing;
	 *
	 * @
	 */
	public LocalDate getBirthDate() {
		return this.birthDate;
	}

	/*
	 * @ requires type != null; ensures \result == type; assignable this.type;
	 *
	 * @
	 */
	public void setType(PetType type) {
		this.type = type;
	}

	/*
	 * @ ensures \result == type; assignable \nothing;
	 *
	 * @
	 */
	public PetType getType() {
		return this.type;
	}

	/*
	 * @ ensures \result == visits; assignable \nothing;
	 *
	 * @
	 */
	public Collection<Visit> getVisits() {
		return this.visits;
	}

	/*
	 * @ requires visit != null; ensures getVisits().contains(visit); assignable visits;
	 *
	 * @
	 */
	public void addVisit(Visit visit) {
		getVisits().add(visit);
	}

}
