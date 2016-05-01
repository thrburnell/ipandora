let nextGivenId = 1

export const addGiven = (formula) => {
  return {
    type: 'ADD_GIVEN',
    id: nextGivenId++,
    formula
  }
}

