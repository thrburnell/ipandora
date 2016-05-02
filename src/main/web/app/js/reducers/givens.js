const givens = (state = [], action) => {
  switch (action.type) {
    case 'ADD_GIVEN':
      return [
        ...state,
        action.id
      ]
    default:
      return state
  }
}

export default givens

