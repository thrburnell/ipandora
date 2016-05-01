import React from 'react'
import Given from './Given'

const GivensList = ({ givens }) => (
  <div>
    <h2>Givens</h2>
    { givens.map(given =>
      <Given
        key={given.id}
        {...given}
      />
    )}
  </div>
)

export default GivensList

