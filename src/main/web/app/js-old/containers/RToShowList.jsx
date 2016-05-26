import { connect } from 'react-redux'
import FormulaList from '../components/FormulaList'

const mapStateToProps = (state) => (
  {
    formulas: state.toShows
  }
)

const RToShowList = connect(
  mapStateToProps
)(FormulaList)

export default RToShowList

