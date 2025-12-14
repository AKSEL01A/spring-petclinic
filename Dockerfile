FROM maven:3.9.11-eclipse-temurin-21
WORKDIR /app

COPY . .

RUN mvn clean package -DskipTests

EXPOSE 8080
ENTRYPOINT ["java", "-jar", "target/spring-petclinic-4.0.0-SNAPSHOT.jar"]
